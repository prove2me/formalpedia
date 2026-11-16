-- Prove2me | Definitions.Def_FiniteSampleDependence_Rigidity_Supplement_Circuits
-- name    : FiniteSampleDependence_Rigidity_Supplement_Circuits
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T10:48:54.988768+00:00
-- url     : https://prove2.me/theorems/90391104-3676-4a6a-82f7-494e7b98b169
-- title:
--   Arithmetic circuits over $\mathbb Q$, their binary encoding, the DPI-recognition language and the family $F_A$
-- statement:
--   This file fixes the decision problem of Theorem D.1 (Appendix D).
--
--   1. **Arithmetic circuits.** For an alphabet size $n$, a circuit is a list of gates $g_0,\dots,g_{s-1}$; each gate is an input variable $U_{i\alpha}$ ($i,\alpha<n$), a rational constant, or the sum, difference or product of two earlier gates. The circuit is well formed when it has at least one gate and every reference is in range; it computes the polynomial in $\mathbb Q[U_{i\alpha}]$ at its last gate.
--   2. **Binary encoding.** A natural number $k$ is written self-delimitingly as $|\mathrm{bits}(k)|$ ones, a zero, and the binary digits of $k$; an integer is a sign bit and its absolute value; a rational is its reduced numerator and its denominator. A gate is a tag $0,\dots,4$ followed by its arguments, and an instance $(n,C)$ is $n$, the number of gates, then the gates.
--   3. **DPI recognition.** $\mathrm{DPIRec}\subseteq\{0,1\}^*$ is the set of codes of instances $(n,C)$ with $n\ge2$, $C$ well formed, whose polynomial $F$ (coefficients read in $\mathbb R$) satisfies (LF-DPI) on $\Delta_{n,n}$:
--   $$F(TU)\le F(U)\qquad\text{for every }U\in\Delta_{n,n}\text{ and every real column-stochastic }T\in\mathbb R^{n\times n}.$$
--   A string that is not the code of such an instance is outside $\mathrm{DPIRec}$.
--   4. **The family $F_A$.** For $A\in\mathbb Q^{n\times n}$,
--   $$F_A(U)=(\det U)^2\,c(U)^\top A\,c(U),\qquad c(U)=U^\top\mathbf 1_n,$$
--   both as a polynomial in $\mathbb Q[U_{i\alpha}]$ and as a real function; a proved sanity lemma checks that the two agree.
--   5. **coNP-hardness.** A language $L$ is coNP-hard if every coNP language over every finite nonempty alphabet reduces to $L$ by a polynomial-time many-one reduction, in the sense of the published Cook framework (one-tape Turing machines, $\mathrm{coNP}$, $\le_p$).
--
--   **Formalization Note** The paper fixes no particular circuit encoding; this one is a standard prefix-free binary encoding, under which decoding is unique and polynomial time. Circuits contain no division gates, as in the paper's "+, −, ×" model; the polynomial of an ill-formed circuit is a junk value that never matters because such codes are outside the language.
-- source:
--   Yuqing Kong, Limits of Finite-Sample Dependence Measures under Data Processing Inequality, STOC 2027 submission #152 (October 2026; SHA-256 f5e620d74cb49d294e046590e96036aa28bf617d4b212a292b7bb68435363118), Appendix D, Theorem D.1 and its proof, PDF p. 27 (printed p. 26); coNP and polynomial-time reductions from the published CookPvsNP_defs

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_FiniteSampleDependence_Rigidity_Model
import Definitions.Def_FiniteSampleDependence_Rigidity_PolynomialAlgebra

/-!
# Appendix D objects: arithmetic circuits, their binary encoding, DPI recognition, `F_A`

Yuqing Kong, *Limits of Finite-Sample Dependence Measures under Data Processing Inequality*,
STOC 2027 submission #152 (October 2026), Appendix D, Theorem D.1, PDF p. 27 (printed p. 26).

Conventions.
* An instance is a pair `(n, C)`: the alphabet size `n` (part of the input) and an arithmetic
  circuit `C` over `ℚ` in the `n²` variables `U_{iα}` (`i, α < n`). The gates are input variables,
  rational constants, `+`, `−` and `×`; gate `k` may only read gates with smaller index, and the
  last gate is the output.
* Strings are over `Bool`. A natural number `k` is written self-delimitingly as `|bits k|` ones,
  a zero, then the binary digits of `k` (`Nat.bits`, least significant first); an integer is a sign
  bit followed by its absolute value; a rational is its (reduced) numerator and its denominator.
  A gate is its tag `0,…,4` followed by its arguments; an instance is `n`, the number of gates,
  then the gates in order.
* `DPIRec` is the set of codes of instances with `n ≥ 2`, a well-formed circuit, and output
  polynomial (coefficients cast to `ℝ`) satisfying (LF-DPI) on `Δ_{n,n}`. A string that is not
  such a code (including the code of an ill-formed circuit) is outside `DPIRec`.
* coNP-hardness is under polynomial-time many-one reductions from every coNP language over every
  finite nonempty alphabet, with the published `CookPvsNP` definitions.
-/

namespace FiniteSampleDependence.Rigidity.Supplement

open Matrix MvPolynomial

/-- A gate of an arithmetic circuit over `ℚ` in the matrix entries `U_{iα}`. -/
inductive Gate where
  /-- the input variable `U_{iα}` -/
  | var (i α : ℕ)
  /-- a rational constant -/
  | const (q : ℚ)
  /-- the sum of gates `j` and `k` -/
  | add (j k : ℕ)
  /-- the difference of gates `j` and `k` -/
  | sub (j k : ℕ)
  /-- the product of gates `j` and `k` -/
  | mul (j k : ℕ)

/-- An arithmetic circuit: its gates in topological order (a straight-line program); the last
gate is the output. -/
structure Circuit where
  gates : List Gate

/-- A circuit is well formed for alphabet size `n`: it has at least one gate, every input
variable `U_{iα}` has `i, α < n`, and every operation gate reads only gates with smaller index. -/
def Circuit.WellFormed (n : ℕ) (C : Circuit) : Prop :=
  C.gates ≠ [] ∧ ∀ (k : ℕ) (h : k < C.gates.length),
    match C.gates[k] with
    | .var i α => i < n ∧ α < n
    | .const _ => True
    | .add j l => j < k ∧ l < k
    | .sub j l => j < k ∧ l < k
    | .mul j l => j < k ∧ l < k

/-- The polynomial in `ℚ[U_{iα} : i, α < n]` computed by a gate, given the polynomials of the
earlier gates (out-of-range references, which well-formedness excludes, read `0`). -/
noncomputable def gatePoly (n : ℕ) (prior : List (MvPolynomial (Fin n × Fin n) ℚ)) :
    Gate → MvPolynomial (Fin n × Fin n) ℚ
  | .var i α => if h : i < n ∧ α < n then X (⟨i, h.1⟩, ⟨α, h.2⟩) else 0
  | .const q => C q
  | .add j k => prior.getD j 0 + prior.getD k 0
  | .sub j k => prior.getD j 0 - prior.getD k 0
  | .mul j k => prior.getD j 0 * prior.getD k 0

/-- The polynomials computed at all gates, in order. -/
noncomputable def gatePolys (n : ℕ) (gs : List Gate) : List (MvPolynomial (Fin n × Fin n) ℚ) :=
  gs.foldl (fun acc g => acc ++ [gatePoly n acc g]) []

/-- The polynomial computed by the circuit: the one at its last gate. -/
noncomputable def Circuit.poly (n : ℕ) (C : Circuit) : MvPolynomial (Fin n × Fin n) ℚ :=
  (gatePolys n C.gates).getLastD 0

/-- Self-delimiting binary code of a natural number. -/
def encodeNat (k : ℕ) : List Bool :=
  List.replicate k.bits.length true ++ [false] ++ k.bits

/-- Binary code of an integer: sign bit, then the absolute value. -/
def encodeInt (z : ℤ) : List Bool :=
  decide (z < 0) :: encodeNat z.natAbs

/-- Binary code of a rational: reduced numerator, then denominator. -/
def encodeRat (q : ℚ) : List Bool :=
  encodeInt q.num ++ encodeNat q.den

/-- Binary code of a gate: a tag `0,…,4`, then its arguments. -/
def encodeGate : Gate → List Bool
  | .var i α => encodeNat 0 ++ encodeNat i ++ encodeNat α
  | .const q => encodeNat 1 ++ encodeRat q
  | .add j k => encodeNat 2 ++ encodeNat j ++ encodeNat k
  | .sub j k => encodeNat 3 ++ encodeNat j ++ encodeNat k
  | .mul j k => encodeNat 4 ++ encodeNat j ++ encodeNat k

/-- Binary code of an instance `(n, C)`: `n`, the number of gates, then the gates. -/
def encodeInstance (n : ℕ) (C : Circuit) : List Bool :=
  encodeNat n ++ encodeNat C.gates.length ++ C.gates.flatMap encodeGate

/-- The real functional `U ↦ F(U)` of a rational polynomial `F` in the `n × n` matrix entries
(coefficients cast to `ℝ`). -/
noncomputable def ratPolyFun {n : ℕ} (F : MvPolynomial (Fin n × Fin n) ℚ) :
    Matrix (Fin n) (Fin n) ℝ → ℝ :=
  polyFun (MvPolynomial.map (algebraMap ℚ ℝ) F)

/-- The DPI-recognition language of Theorem D.1: codes of instances `(n, C)` with `n ≥ 2`, `C` a
well-formed circuit, and the polynomial computed by `C` satisfying (LF-DPI) on `Δ_{n,n}`
(`F(TU) ≤ F(U)` for every `U ∈ Δ_{n,n}` and every real column-stochastic `T`). -/
def DPIRec : CookPvsNP.Lang Bool :=
  {s | ∃ (n : ℕ) (C : Circuit), 2 ≤ n ∧ C.WellFormed n ∧ s = encodeInstance n C ∧
    LFDPI (ratPolyFun (C.poly n))}

/-- The column sum `c_α = ∑_i U_{iα}` as a rational polynomial. -/
noncomputable def colSumPoly (n : ℕ) (α : Fin n) : MvPolynomial (Fin n × Fin n) ℚ :=
  ∑ i : Fin n, X (i, α)

/-- `F_A(U) = (det U)² c(U)ᵀ A c(U)` as a polynomial in `ℚ[U_{iα}]`, for `A ∈ ℚ^{n×n}`. -/
noncomputable def faPoly (n : ℕ) (A : Matrix (Fin n) (Fin n) ℚ) : MvPolynomial (Fin n × Fin n) ℚ :=
  (Matrix.mvPolynomialX (Fin n) (Fin n) ℚ).det ^ 2 *
    ∑ α : Fin n, ∑ β : Fin n, C (A α β) * colSumPoly n α * colSumPoly n β

/-- `F_A(U) = (det U)² c(U)ᵀ A c(U)` as a real functional, with `c(U) = Uᵀ 1ₙ` the column
marginal and the entries of `A` cast to `ℝ`. -/
noncomputable def faFun {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (U : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  U.det ^ 2 * (colMarginal U ⬝ᵥ (A.map (Rat.cast : ℚ → ℝ) *ᵥ colMarginal U))

/-- coNP-hardness under polynomial-time many-one reductions: every coNP language over every
finite nonempty alphabet reduces to `L`. -/
def CoNPHard {Sym : Type} (L : CookPvsNP.Lang Sym) : Prop :=
  ∀ (Sym' : Type) [Fintype Sym'] [Nonempty Sym'] (L' : CookPvsNP.Lang Sym'),
    L' ∈ CookPvsNP.coNP Sym' → CookPvsNP.PolyReducible L' L

/-- Sanity check of the encoding: `F_A` evaluated through its polynomial is `faFun A`. -/
theorem ratPolyFun_faPoly {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (U : Matrix (Fin n) (Fin n) ℝ) :
    ratPolyFun (faPoly n A) U = faFun A U := by
  unfold ratPolyFun polyFun faPoly faFun
  rw [MvPolynomial.eval_map, ← MvPolynomial.coe_eval₂Hom, map_mul, map_pow, RingHom.map_det]
  have hX : (eval₂Hom (algebraMap ℚ ℝ) (fun p : Fin n × Fin n => U p.1 p.2)).mapMatrix
      (Matrix.mvPolynomialX (Fin n) (Fin n) ℚ) = U := by
    ext i j; simp [Matrix.mvPolynomialX_apply]
  rw [hX]
  congr 1
  simp [map_sum, colSumPoly, dotProduct, mulVec, colMarginal, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

end FiniteSampleDependence.Rigidity.Supplement


