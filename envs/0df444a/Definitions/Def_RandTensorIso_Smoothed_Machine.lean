-- Prove2me | Definitions.Def_RandTensorIso_Smoothed_Machine
-- name    : RandTensorIso_Smoothed_Machine
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T01:38:04.422833+00:00
-- url     : https://prove2.me/theorems/b7df4de4-ff45-49de-ab0d-c19682206144
-- title:
--   Bit encodings, deterministic programs, strict-threshold orbit guarantees, and Algorithm 3
-- statement:
--   The paper's algorithms are deterministic and run on rationals and Gaussian rationals "encoded in the usual way". Here a **program** is a Mathlib multi-stack Turing machine (`Turing.FinTM2`) whose input and output stack alphabets are $\{0,1\}$. On input $w$ it starts with $w$ on the input stack; it **halts within $T$ steps with output $o$** if after at most $T$ steps it reaches a configuration with no current instruction, and its output stack then holds $o$ (other stacks may be nonempty). **Encodings:** a natural number in binary, least significant bit first, each bit $b$ written as $1b$ and terminated by $0$; an integer as a sign bit and its absolute value; a rational in lowest terms as numerator and denominator; a Gaussian rational $s+it$ as $s$ then $t$; tensors and matrices entrywise in lexicographic order. A complex tensor **specified to $\ell$ bits of precision** is written as $\ell$ followed by the integers $2^\ell\operatorname{Re}\tilde A(p)$ and $2^\ell\operatorname{Im}\tilde A(p)$ of its truncation $\tilde A$ (fixed point, exactly $\ell$ fractional digits).
--
--   **Problem 1 (gapped unitary orbit approximation)** asks, given $A,B$, $\varepsilon$ and $\gamma$, to distinguish $\operatorname{dist}_{\mathbb C}(A,B)<\varepsilon$ from $\operatorname{dist}_{\mathbb C}(A,B)>\gamma\varepsilon$. An output is **correct** if: when $\operatorname{dist}_{\mathbb C}(A,B)<\varepsilon$ it is YES together with $(\hat L,\hat R,\hat T)$, unitary matrices with entries in $\mathbb Q(i)$ and $\|(\hat L,\hat R,\hat T)\curvearrowright A-B\|_F\le\gamma\varepsilon$; and when $\operatorname{dist}_{\mathbb C}(A,B)>\gamma\varepsilon$ it is NO. Between the thresholds every output is correct. The goal's input is $n$, then $A$ and $B$ each specified to $\ell$ bits, then $\varepsilon$; Algorithm 3's input is $n$, $A,B\in\mathbb Q(i)^{n\times n\times n}$, $\delta$, $\varepsilon$.
--
--   **Formalization Note.** NO is the string `[false]`; YES is `true` followed by the encodings of $\hat L,\hat R,\hat T$ (`encYes`); any other string is neither. The number of steps is the running time. A machine is allowed to halt without reading all of its input.
--
--
--   The output relation `Alg3Outputs` now records Algorithm 3 itself: the zero-tensor and ratio tests, the least dyadic scale and least precision, the norm test, sorted approximate Gram eigendecompositions, the gap test on B, exact rational cores, and lexicographic calls to Algorithm A. It accepts the first candidate passing the squared residual test, rounds it within the printed tolerance to unitary Gaussian-rational matrices, or returns NO. The factor in the ratio is $10^8$. `ApproxGramBasis` records the forward-error interface stated on PDF 25; numerical choices satisfying that interface and the unspecified rounding choices are universally covered by Theorem 2.14. `ImplementsAlg3` requires a program to halt with an operationally permitted output on every valid input. No orbit-correctness assumption is built into the algorithm relation.
--
--   The predicate `GappedCorrect` records the strict thresholds of Theorems 1.1, 2.10 and 2.14. Problem 1 itself is printed with non-strict thresholds; this definition follows the theorem conclusions being formalized.
-- source:
--   Chizewer, Everett, Mithal, Qiao, Random tensor isomorphism under orthogonal and unitary actions: Smoothed and average-case analysis, STOC 2027 submission (manuscript sha256 f4a12b77…), pp. 5–6, 14, 24, 26, 30 (PDF 7–8, 16, 26, 28, 32), Problem 1, §2 preamble (encoding of ℚ(i)), Algorithm 3 input, (2.5); PDF 25 (numerical forward-error interface), PDF 28 (Algorithm 3), PDF 62 (Algorithm A)

import Mathlib
import Definitions.Def_RandTensorIso_Smoothed_Tensor
import Definitions.Def_RandTensorIso_Smoothed_Seed

namespace RandTensorIso.Smoothed

open Matrix
open scoped Classical

/-! ### Binary encodings (all self-delimiting, over the alphabet `Bool`) -/

/-- A natural number in binary (least significant bit first), each bit `b` written as
`true, b`, terminated by `false`. -/
def encNat (m : ℕ) : List Bool := (Nat.bits m).flatMap (fun b => [true, b]) ++ [false]

/-- An integer: a sign bit (`true` for negative), then its absolute value. -/
def encInt (z : ℤ) : List Bool := decide (z < 0) :: encNat z.natAbs

/-- A rational in lowest terms: numerator, then denominator. -/
def encRat (q : ℚ) : List Bool := encInt q.num ++ encNat q.den

/-- A Gaussian rational `s + i t`: `s`, then `t`. -/
def encGQ (z : GQ) : List Bool := encRat z.1 ++ encRat z.2

/-- A tensor with entries in `ℚ(i)`, entrywise in lexicographic order of `(i, j, k)`. -/
def encGTensor {n : ℕ} (A : GTensor n) : List Bool :=
  (List.finRange n).flatMap fun i => (List.finRange n).flatMap fun j =>
    (List.finRange n).flatMap fun k => encGQ (A (i, j, k))

/-- An `n × n` matrix with entries in `ℚ(i)`, entrywise in lexicographic order of `(i, j)`. -/
def encGMat {n : ℕ} (X : Matrix (Fin n) (Fin n) GQ) : List Bool :=
  (List.finRange n).flatMap fun i => (List.finRange n).flatMap fun j => encGQ (X i j)

/-- A complex tensor specified to `ℓ` bits after the binary point (fixed point): the precision
`ℓ`, then, entrywise in lexicographic order, the integers `truncNum ℓ (Re A_p)` and
`truncNum ℓ (Im A_p)`, i.e. the binary digits of the truncation `Ã` with exactly `ℓ` fractional
digits. -/
noncomputable def encFixedTensor {n : ℕ} (ℓ : ℕ) (A : Tensor3 n) : List Bool :=
  encNat ℓ ++ ((List.finRange n).flatMap fun i => (List.finRange n).flatMap fun j =>
    (List.finRange n).flatMap fun k =>
      encInt (truncNum ℓ (A (i, j, k)).re) ++ encInt (truncNum ℓ (A (i, j, k)).im))

/-! ### The machine: a Mathlib multi-stack Turing machine (`Turing.FinTM2`) over bits -/

/-- A deterministic program: a Mathlib `Turing.FinTM2` whose input-stack and output-stack
alphabets are identified with `Bool`. -/
structure Program where
  /-- the machine -/
  tm : Turing.FinTM2
  /-- the input alphabet is `Bool` -/
  inAlph : tm.Γ tm.k₀ ≃ Bool
  /-- the output alphabet is `Bool` -/
  outAlph : tm.Γ tm.k₁ ≃ Bool

/-- The configuration after `t` steps on input `w` (written on the input stack, first symbol on
top), or `none` if the machine halted earlier. -/
def Program.cfgAt (P : Program) (w : List Bool) (t : ℕ) : Option P.tm.Cfg :=
  (fun c => c.bind P.tm.step)^[t] (some (Turing.initList P.tm (w.map P.inAlph.symm)))

/-- On input `w` the program halts after at most `T` steps (it reaches a configuration whose
label is `none`), and the output stack then holds `out` (top symbol first). Other stacks may be
nonempty at halting. -/
def Program.HaltsWith (P : Program) (w out : List Bool) (T : ℕ) : Prop :=
  ∃ t ≤ T, ∃ c : P.tm.Cfg, P.cfgAt w t = some c ∧
    (c : Turing.TM2.Cfg P.tm.Γ P.tm.Λ P.tm.σ).l = none ∧
    ((c : Turing.TM2.Cfg P.tm.Γ P.tm.Λ P.tm.σ).stk P.tm.k₁).map P.outAlph = out

/-! ### Strict-threshold answers used in Theorems 1.1, 2.10 and 2.14 -/

/-- The output `NO`. -/
def encNo : List Bool := [false]

/-- The output `YES` with the witness `(L̂, R̂, T̂)`, matrices with entries in `ℚ(i)`. -/
def encYes {n : ℕ} (L R T : Matrix (Fin n) (Fin n) GQ) : List Bool :=
  true :: (encGMat L ++ encGMat R ++ encGMat T)

/-- Correctness of an output `out` for the gapped unitary orbit approximation problem
(the strict-threshold version in Theorems 1.1, 2.10 and 2.14) on `A, B`:
if `dist_ℂ(A, B) < ε`, then `out` is `YES` with a witness `(L̂, R̂, T̂)` of unitary matrices with
entries in `ℚ(i)` and `‖(L̂, R̂, T̂) ↷ A − B‖_F ≤ γε`; if `dist_ℂ(A, B) > γε`, then `out` is `NO`.
In between, every output is correct. -/
def GappedCorrect {n : ℕ} (A B : Tensor3 n) (ε γ : ℝ) (out : List Bool) : Prop :=
  (distC A B < ε → ∃ L R T : Matrix (Fin n) (Fin n) GQ, out = encYes L R T ∧
      gqMat L ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ gqMat R ∈ Matrix.unitaryGroup (Fin n) ℂ ∧
      gqMat T ∈ Matrix.unitaryGroup (Fin n) ℂ ∧
      frob (act (gqMat L) (gqMat R) (gqMat T) A - B) ≤ γ * ε) ∧
  (γ * ε < distC A B → out = encNo)

/-- The input of the goal's program: `n`, then `A` and `B` specified to `ℓ` bits after the binary
point (`ℓ` written once per tensor), then the rational `ε`. -/
noncomputable def goalInput {n : ℕ} (ℓ : ℕ) (A B : Tensor3 n) (ε : ℚ) : List Bool :=
  encNat n ++ encFixedTensor ℓ A ++ encFixedTensor ℓ B ++ encRat ε

/-- The input format of Algorithm 3 (and of Theorem 2.10's algorithm): `n`, the tensors
`A, B ∈ ℚ(i)^{n×n×n}`, then the rationals `δ` and `ε`. -/
def alg3Input {n : ℕ} (A B : GTensor n) (δ ε : ℚ) : List Bool :=
  encNat n ++ encGTensor A ++ encGTensor B ++ encRat δ ++ encRat ε

/-! ### Algorithm 3, PDF 28: operational output relation

The numerical subroutine is represented by its forward-error interface (PDF 25), not by
assuming the orbit-decision conclusion. All choices satisfying that interface are allowed.
The theorem asserts correctness for every such run and existence of a bit-machine implementation.
-/

/-- Frobenius norm of a square complex matrix. -/
noncomputable def matFrob {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  Real.sqrt (∑ i, ∑ j, ‖X i j‖ ^ 2)

/-- A permitted numerical eigendecomposition in Step 3: rational approximate eigenvectors and
sorted eigenvalues with the forward-error bounds stated on PDF 25. The exact eigenbasis is
only used to specify the error; it is not an input to the bit machine. -/
def ApproxGramBasis {n : ℕ} (A : Tensor3 n) (d : Fin 3) (ℓ : ℕ)
    (W : Matrix (Fin n) (Fin n) GQ) (eigvals : Fin n → ℚ) : Prop :=
  Antitone eigvals ∧ ∃ V : U n, IsGramEigBasis d A V ∧
    opNorm (gqMat W - (V : Matrix (Fin n) (Fin n) ℂ)) ≤
      n * (⨆ i : Fin n, ⨆ j : Fin n, ‖(V : Matrix (Fin n) (Fin n) ℂ) i j‖) * (2 : ℝ)⁻¹ ^ ℓ ∧
    (∀ i, |(eigvals i : ℝ) - gramEig d A i| ≤
      n * opNorm (gram d A) * (2 : ℝ)⁻¹ ^ ℓ)

/-- Step 1's least dyadic upper bound for the nonzero tensor norm. -/
noncomputable def alg3Scale {n : ℕ} (A : Tensor3 n) : ℝ :=
  (2 : ℝ) ^ (⌈Real.log (frob A) / Real.log 2⌉ : ℤ)

/-- Step 1's least precision; used only after the zero-tensor test, for n ≥ 1 and ε > 0. -/
noncomputable def alg3Precision {n : ℕ} (A : Tensor3 n) (ε : ℚ) : ℕ :=
  sInf {k : ℕ | (2 : ℝ)⁻¹ ^ k ≤ min ((ε : ℝ) / alg3Scale A) 1 / (10 ^ 6 * n ^ 5)}

/-- The three candidate transformations Ṽ_d diag(z_d) Ũ_d*. -/
def alg3Candidate {n : ℕ} (W V : Fin 3 → Matrix (Fin n) (Fin n) GQ)
    (z : Fin 3 → Fin n → GQ) (d : Fin 3) : Matrix (Fin n) (Fin n) ℂ :=
  gqMat (V d) * diagonal (fun i => GQ.toC (z d i)) * (gqMat (W d))ᴴ

/-- Steps 5–6: visit pairs in the supplied order, skip FAIL and failed residual tests, round
and return the first passing candidate, or return NO at the end. The rounding tolerance is
exactly 9√n(2n+1)²·4n²2^{-ℓ} from Step 5. -/
def Alg3Search {n : ℕ} (A B : Tensor3 n) (S S' : GTensor n)
    (W V : Fin 3 → Matrix (Fin n) (Fin n) GQ) (γ ε : ℝ) (ℓ : ℕ) :
    List (Fin n × Fin n) → List Bool → Prop
  | [], out => out = encNo
  | ij :: rest, out =>
      ∃ phases : Option (Fin 3 → Fin n → GQ), AlgAOutputs S S' ij.1 ij.2 (1 / 12) ℓ phases ∧
        match phases with
        | none => Alg3Search A B S S' W V γ ε ℓ rest out
        | some z =>
          let X := alg3Candidate W V z
          if frob (act (X 0) (X 1) (X 2) A - B) ^ 2 ≤ (γ * ε / 2) ^ 2 then
            ∃ H : Fin 3 → Matrix (Fin n) (Fin n) GQ,
              (∀ d, gqMat (H d) ∈ Matrix.unitaryGroup (Fin n) ℂ ∧
                matFrob (gqMat (H d) - X d) ≤
                  9 * Real.sqrt n * (2 * n + 1) ^ 2 * (4 * n ^ 2 * (2 : ℝ)⁻¹ ^ ℓ)) ∧
              out = encYes (H 0) (H 1) (H 2)
          else Alg3Search A B S S' W V γ ε ℓ rest out

/-- Algorithm 3's complete operational relation, with admissible numerical and rounding
choices. It computes exact cores, performs the gap test on B's approximate eigenvalues,
and enumerates seed pairs in lexicographic order. No correctness condition occurs here. -/
def Alg3Outputs {n : ℕ} (A B : GTensor n) (δ ε : ℚ) (out : List Bool) : Prop :=
  let Ac := GTensor.toC A
  let Bc := GTensor.toC B
  let γ := (10 : ℝ) ^ 8 * ⌈Real.sqrt n⌉₊ * frob Ac ^ 3 / δ
  if Ac = 0 then out = encNo
  else if γ < 2 then out = encNo
  else
    let ℓ := alg3Precision Ac ε
    if |frob Ac - frob Bc| > ε then out = encNo
    else ∃ (W V : Fin 3 → Matrix (Fin n) (Fin n) GQ) (eigA eigB : Fin 3 → Fin n → ℚ),
      (∀ d, ApproxGramBasis Ac d ℓ (W d) (eigA d) ∧ ApproxGramBasis Bc d ℓ (V d) (eigB d)) ∧
      if ∃ (d : Fin 3) (i j : Fin n), j.val = i.val + 1 ∧ eigB d i - eigB d j < δ / 2 then
        out = encNo
      else ∃ S S' : GTensor n,
        GTensor.toC S = act (gqMat (W 0))ᴴ (gqMat (W 1))ᴴ (gqMat (W 2))ᴴ Ac ∧
        GTensor.toC S' = act (gqMat (V 0))ᴴ (gqMat (V 1))ᴴ (gqMat (V 2))ᴴ Bc ∧
        Alg3Search Ac Bc S S' W V γ ε ℓ
          ((List.finRange n).flatMap fun i => (List.finRange n).map fun j => (i, j)) out

/-- A program implements Algorithm 3 if, on every valid input, it halts with the output of
an operational run. Runtime is imposed separately by the theorem. -/
def ImplementsAlg3 (P : Program) : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ (A B : GTensor n) (δ ε : ℚ), 0 < δ → 0 < ε →
    ∃ (out : List Bool) (T : ℕ), P.HaltsWith (alg3Input A B δ ε) out T ∧ Alg3Outputs A B δ ε out

end RandTensorIso.Smoothed


