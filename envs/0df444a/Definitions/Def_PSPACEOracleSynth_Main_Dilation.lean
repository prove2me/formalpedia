-- Prove2me | Definitions.Def_PSPACEOracleSynth_Main_Dilation
-- name    : PSPACEOracleSynth_Main_Dilation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T03:21:06.822366+00:00
-- url     : https://prove2.me/theorems/67d537d3-702e-4d09-974d-10f33fd87b92
-- title:
--   Dilations, the projective classes $\mathsf{projUnitaryP}^A$, $\mathsf{projUnitaryPSPACE}^A$, and the language $\mathcal U\otimes\mathcal U^\dagger$
-- statement:
--   Let $\iota_a|\psi\rangle=|\psi\rangle|0^a\rangle$ append $a$ ancillas in state $|0\rangle$.
--
--   1. (**Definition 2.2**) A unitary $\tilde U$ on $n+a$ qubits is an **$a$-qubit dilation of $U_n$ with garbage state $|g\rangle$** if
--   $$\tilde U(|\psi\rangle|0^a\rangle)=(U_n|\psi\rangle)|g\rangle\qquad\text{for every }|\psi\rangle;$$
--   it is a **dilation** of $U_n$ if this holds for some $|g\rangle$ (one $|g\rangle$ for all inputs). An extension ($|g\rangle=|0^a\rangle$) is a special dilation.
--   2. (**Definition 2.3**, projective classes) $\mathcal U\in\mathsf{projUnitaryP}^A$ if there are a time-uniform family $(C_{n,m})$ of unitary circuits whose only oracle gates are $O_A$, of width at most $n+p(n+m)$ for a polynomial $p$, and for all $n,m$ a dilation $\tilde U_{n,m}$ of $U_n$ with
--   $$\|C^A_{n,m}-\tilde U_{n,m}\|\le 2^{-m}.$$
--   $\mathsf{projUnitaryPSPACE}^A$ is defined in the same way with space-uniform families (which may have exponentially many gates).
--   3. (**§4.3**) $\mathcal U\otimes\mathcal U^\dagger$ is the unitary language whose member on $2n$ qubits is $U_n\otimes U_n^\dagger$ ($U_n$ on the first $n$ qubits, $U_n^\dagger$ on the last $n$) and whose members on an odd number of qubits are identities.
--
--   The norm $\|\cdot\|$ is the operator norm. In the projective classes the global phase of $U_n$ does not count; these classes and $\mathcal U\otimes\mathcal U^\dagger$ are the objects of Theorem 1.1 and Lemmas 4.5–4.6.
--
--   **Formalization Note.** The bodies of `projUnitaryP`/`projUnitaryPSPACE` copy those of the published clean classes `KTUnitary.Synth.unitaryP`/`unitaryPSPACE` (one FPTEAS encoding per family, descriptions generated from `tup [1^n, 1^l]`, precision $2^{-l}$, width $n\le N\le n+p(n+l)$), with `IsDilation` in place of `IsExtension` and with `UCircuit.Plain` (only uncontrolled $O_A$ gates; $O_A^*,O_A^\dagger,O_A^T$ equal $O_A$). Data occupy the first $n$ wires and ancillas the last $N-n$ (`ancPad`). Unitary languages are indexed by $n\in\mathbb N$ (published `ULang`), so $n=0$ and $l=0$ are included. `opNormR` is the operator norm of a rectangular matrix; `ancMat` is $\iota_a$ and `dilMat h U g` is $|\psi\rangle\mapsto(U|\psi\rangle)\otimes|g\rangle$.
-- source:
--   Sichen Wang, Unitary Synthesis with a PSPACE Oracle, STOC 2027 submission #1740 (October 2026), Definition 2.2 and Definition 2.3, p. 10; §2.4, p. 13 (the map U ⊗ |g⟩); §4.3, p. 28 (the language U ⊗ U†)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Complexity
import Definitions.Def_QAdvFew_PoQOracle_Oracle
import Definitions.Def_QAdvFew_PoQOracle_tup
import Definitions.Def_KTUnitary_Synth_ULang
import Definitions.Def_KTUnitary_Synth_emb
import Definitions.Def_KTUnitary_Synth_UCircuit
import Definitions.Def_KTUnitary_Synth_ancPad
import Definitions.Def_KTUnitary_Synth_IsExtension
import Definitions.Def_KTUnitary_Synth_opNorm
import Definitions.Def_KTUnitary_Synth_HasFPTEAS
import Definitions.Def_KTUnitary_Synth_TimeUniform
import Definitions.Def_KTUnitary_Synth_SpaceUniform

open QAlgorithms.Complexity QAdvFew.PoQOracle KTUnitary.Synth

namespace PSPACEOracleSynth.Main

/-!
# Dilations, the projective classes, and the language `U ⊗ U†`

Sichen Wang, *Unitary Synthesis with a PSPACE Oracle*, STOC 2027 submission #1740 (October 2026),
§2.1–§2.2, pp. 9–10 (Definitions 2.2 and 2.3), §2.4, p. 13, and §4.3, p. 28.

Wire conventions are those of the published `KTUnitary.Synth.ancPad`: on `N ≥ n` qubits the data
occupy wires `0, …, n − 1` and the `a = N − n` ancillas wires `n, …, N − 1`.
-/

/-- The operator norm of a rectangular matrix `A : ℂ^ι → ℂ^κ` between Euclidean spaces (the largest
singular value). For square matrices it is the published `KTUnitary.Synth.opNorm`. -/
noncomputable def opNormR {κ ι : Type} [Fintype κ] [Fintype ι] [DecidableEq ι]
    (A : Matrix κ ι ℂ) : ℝ :=
  ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin A)‖

/-- The data part `z₀ ⋯ z_{n−1}` of a basis state `z` of `N ≥ n` qubits. -/
def dataPart {n N : ℕ} (h : n ≤ N) (z : Bits N) : Bits n := fun r => z (Fin.castLE h r)

/-- The ancilla part `z_n ⋯ z_{N−1}` of a basis state `z` of `N ≥ n` qubits. -/
def ancPart {n N : ℕ} (h : n ≤ N) (z : Bits N) : Bits (N - n) :=
  fun r => z ⟨n + r.val, by have := r.isLt; omega⟩

/-- The product vector `|φ⟩ ⊗ |g⟩` on `N ≥ n` qubits, with `φ` on the first `n` wires and `g` on the
last `N − n` wires. With `g = |0^a⟩` it is the published `ancPad h φ`. -/
def tensorPad {n N : ℕ} (h : n ≤ N) (φ : Bits n → ℂ) (g : Bits (N - n) → ℂ) : Bits N → ℂ :=
  fun z => φ (dataPart h z) * g (ancPart h z)

/-- The isometry `ι_a : |ψ⟩ ↦ |ψ⟩|0^a⟩` as a `2^N × 2^n` matrix (p. 9). Column `x` is
`ancPad h |x⟩`. -/
noncomputable def ancMat {n N : ℕ} (h : n ≤ N) : Matrix (Bits N) (Bits n) ℂ :=
  Matrix.of fun z x => ancPad h (Pi.single x 1) z

/-- The matrix of `|ψ⟩ ↦ (U|ψ⟩) ⊗ |g⟩` from `n` to `N ≥ n` qubits (written `U ⊗ |g⟩` on p. 13). -/
def dilMat {n N : ℕ} (h : n ≤ N) (U : Matrix (Bits n) (Bits n) ℂ) (g : Bits (N - n) → ℂ) :
    Matrix (Bits N) (Bits n) ℂ :=
  Matrix.of fun z x => U (dataPart h z) x * g (ancPart h z)

/-- **Dilation with a given garbage state** (Definition 2.2, p. 10): `Ub` on `n + a` qubits is an
`a`-qubit dilation of `U` with garbage state `|g⟩` if `Ub` is unitary and
`Ub(|ψ⟩|0^a⟩) = (U|ψ⟩)|g⟩` for every `|ψ⟩`. -/
def IsDilationWith {n N : ℕ} (h : n ≤ N) (U : Matrix (Bits n) (Bits n) ℂ)
    (Ub : Matrix (Bits N) (Bits N) ℂ) (g : Bits (N - n) → ℂ) : Prop :=
  Ub ∈ Matrix.unitaryGroup (Bits N) ℂ ∧
    ∀ ψ : Bits n → ℂ, Ub.mulVec (ancPad h ψ) = tensorPad h (U.mulVec ψ) g

/-- **Dilation** (Definition 2.2, p. 10): `Ub` is a dilation of `U` with some garbage state `|g⟩`
(one `g` for all inputs `ψ`). For unitary `U` and `n`-qubit inputs, `g` is automatically a unit
vector. -/
def IsDilation {n N : ℕ} (h : n ≤ N) (U : Matrix (Bits n) (Bits n) ℂ)
    (Ub : Matrix (Bits N) (Bits N) ℂ) : Prop :=
  ∃ g : Bits (N - n) → ℂ, IsDilationWith h U Ub g

/-- **The class `projUnitaryP^A`** (Definition 2.3, p. 10): as the published clean class
`KTUnitary.Synth.unitaryP (emb A)`, with a dilation in place of the extension, and with circuits
whose oracle gates are uncontrolled `O_A` gates (`UCircuit.Plain`): there are an encoding `f` with an
FPTEAS, a time-uniform family `C n l` (descriptions computed from `tup [1^n, 1^l]`) and a polynomial
`p` such that for all `n, l`: every explicit gate of `C n l` is unitary under `f`, its oracle gates are
plain, `n ≤ N ≤ n + p(n + l)` for its width `N`, and some dilation `Ub` of `U_n` satisfies
`‖Ub − C^A_{n,l}‖ ≤ 2^{−l}`. -/
def projUnitaryP (A : Oracle) : Set ULang :=
  {U | ∃ (f : Str → ℝ) (C : ℕ → ℕ → UCircuit) (p : Polynomial ℕ), HasFPTEAS f ∧
    TimeUniform (fun nl : ℕ × ℕ => tup [unary nl.1, unary nl.2]) (fun nl => (C nl.1 nl.2).code) ∧
    ∀ n l : ℕ, (C n l).Valid f ∧ (C n l).Plain ∧ ∃ h : n ≤ (C n l).N, (C n l).N ≤ n + p.eval (n + l) ∧
      ∃ Ub, IsDilation h (U n : Matrix (Bits n) (Bits n) ℂ) Ub ∧
        opNorm (Ub - (C n l).unitary f (emb A)) ≤ (2 : ℝ)⁻¹ ^ l}

/-- **The class `projUnitaryPSPACE^A`** (Definition 2.3, p. 10): as `projUnitaryP A` with a
space-uniform family (published `KTUnitary.Synth.SpaceUniform`: description length at most
`2^{p'}`, gate descriptions of length at most `p'`, bits decidable in polynomial space without
oracle); the number of gates is not bounded polynomially. -/
def projUnitaryPSPACE (A : Oracle) : Set ULang :=
  {U | ∃ (f : Str → ℝ) (C : ℕ → ℕ → UCircuit) (p : Polynomial ℕ), HasFPTEAS f ∧
    SpaceUniform (fun nl : ℕ × ℕ => tup [unary nl.1, unary nl.2]) (fun nl => (C nl.1 nl.2).code)
      (fun nl => (C nl.1 nl.2).gateCodes) ∧
    ∀ n l : ℕ, (C n l).Valid f ∧ (C n l).Plain ∧ ∃ h : n ≤ (C n l).N, (C n l).N ≤ n + p.eval (n + l) ∧
      ∃ Ub, IsDilation h (U n : Matrix (Bits n) (Bits n) ℂ) Ub ∧
        opNorm (Ub - (C n l).unitary f (emb A)) ≤ (2 : ℝ)⁻¹ ^ l}

/-- The first half `z₀ ⋯ z_{m−1}` of a basis state of `k` qubits, `m = ⌊k/2⌋`. -/
def firstHalf {k : ℕ} (z : Bits k) : Bits (k / 2) := fun r => z ⟨r.val, by have := r.isLt; omega⟩

/-- The second half `z_m ⋯ z_{2m−1}` of a basis state of `k` qubits, `m = ⌊k/2⌋`. -/
def secondHalf {k : ℕ} (z : Bits k) : Bits (k / 2) :=
  fun r => z ⟨k / 2 + r.val, by have := r.isLt; omega⟩

open Classical in
/-- **The unitary language `U ⊗ U†`** (§4.3, p. 28): "the unitary language whose member of length
`2n` is `U_n ⊗ U_n†` and whose members of odd length are identities". On `2n` qubits the first `n`
wires carry `U_n` and the last `n` wires carry `U_n†`: the entry in row `z`, column `z'` is
`⟨z₁|U_n|z'₁⟩ · ⟨z₂|U_n†|z'₂⟩ = U_n(z₁, z'₁) · conj(U_n(z'₂, z₂))` for the halves `z = z₁z₂`,
`z' = z'₁z'₂`. -/
noncomputable def tensorAdj (U : ULang) : ULang :=
  ULang.ofMatrices fun k =>
    if k % 2 = 0 then
      Matrix.of fun z z' =>
        (U (k / 2) : Matrix (Bits (k / 2)) (Bits (k / 2)) ℂ) (firstHalf z) (firstHalf z') *
          star ((U (k / 2) : Matrix (Bits (k / 2)) (Bits (k / 2)) ℂ) (secondHalf z') (secondHalf z))
    else 1

end PSPACEOracleSynth.Main


