-- Prove2me | Definitions.Def_TimeSpaceMA_tensorEncode
-- name    : TimeSpaceMA_tensorEncode
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:57:00.51721+00:00
-- url     : https://prove2.me/theorems/95c6fcc9-5e65-42db-beb9-2d066da4ad10
-- title:
--   Tensor encoding, lines, distance, line test
-- statement:
--   For $\alpha\in[L]^r$, $\mathrm{sources}(\alpha):=S_{\alpha_1}\times\dots\times S_{\alpha_r}$, and the tensor encoding of $z\in A^{[q]^r}$ is
--   $$(G^{\otimes r}z)(\alpha):=\sum_{p\in\mathrm{sources}(\alpha)}z_p.$$
--   Tensor codewords are the words in the image. The line of a word $Y$ through $\alpha$ along axis $i$ lets the $i$-th coordinate range over $[L]$. The distance $\mathrm{dist}(Y,G^{\otimes r})$ is the smallest fraction of positions in which $Y$ differs from a tensor codeword over the same group.
--
--   The **line test** picks a uniform $\alpha\in[L]^r$ and accepts if all $r$ lines through $\alpha$ are codewords. Also defined here: $\kappa_r:=4(2r)^8\delta^{-7r}$, and, for a linear code $C$ over a field, the set $C^{\otimes k}$ of words all of whose axis lines lie in $C$, as in Theorem A.2.
-- source:
--   Williams, Xi, Short Non-Interactive Proofs for Time-Space Computations, STOC 2027 submission (manuscript sha256 184c2f95…), Definitions 3.12, 3.14, pp.12–13; Lemma 3.15, p.13; Theorem A.2, p.32

import Definitions.Def_TimeSpaceMA_SubsetSumCode

namespace TimeSpaceMA

variable {q L r : ℕ}

/-- `sources(α) := S_{α₁} × ⋯ × S_{α_r}`; Definition 3.12, p.12. -/
def sources (G : SubsetSumCode q L) (α : Fin r → Fin L) : Finset (Fin r → Fin q) :=
  Fintype.piFinset fun i => G.supp (α i)

/-- The `r`-fold tensor encoding `(G^{⊗r} z)(α) := Σ_{p ∈ sources(α)} z_p` (Williams, Xi, STOC 2027
submission, manuscript sha256 184c2f95…, Definition 3.12, p.12). -/
def tensorEncode (G : SubsetSumCode q L) {A : Type*} [AddCommMonoid A]
    (z : (Fin r → Fin q) → A) : (Fin r → Fin L) → A :=
  fun α => ∑ p ∈ sources G α, z p

/-- Tensor codewords: the words in the image of `G^{⊗r}`. -/
def IsTensorCodeword (G : SubsetSumCode q L) {A : Type*} [AddCommMonoid A]
    (Y : (Fin r → Fin L) → A) : Prop :=
  ∃ z : (Fin r → Fin q) → A, Y = tensorEncode G z

/-- The line of `Y` through `α` along axis `i`: the `i`-th coordinate of `α` ranges over `[L]`, the
others stay. -/
def line {X A : Type*} (Y : (Fin r → X) → A) (α : Fin r → X) (i : Fin r) : X → A :=
  fun ℓ => Y (Function.update α i ℓ)

open Classical in
/-- Fraction of positions in which two words differ. -/
noncomputable def relHamming {ι A : Type*} [Fintype ι] (w c : ι → A) : ℝ :=
  ((Finset.univ.filter fun i => w i ≠ c i).card : ℝ) / Fintype.card ι

/-- The smallest fraction of positions in which `w` differs from a word of `T`. -/
noncomputable def distToSet {ι A : Type*} [Fintype ι] (w : ι → A) (T : Set (ι → A)) : ℝ :=
  sInf (relHamming w '' T)

/-- `dist(Y, G^{⊗r})`: the smallest fraction of positions in which `Y` differs from a tensor codeword
over the entry group; Definition 3.12, p.12. The set is nonempty (the zero word) and bounded below,
so the infimum is a minimum of finitely many… fractions, and not a junk value. -/
noncomputable def distToTensor (G : SubsetSumCode q L) {A : Type*} [AddCommMonoid A]
    (Y : (Fin r → Fin L) → A) : ℝ :=
  distToSet Y {c | IsTensorCodeword G c}

open Classical in
/-- The rejection probability of the line test (Definition 3.14, p.13): a uniform point `α ∈ [L]^r` is
rejected unless all `r` lines of `Y` through `α` are codewords. -/
noncomputable def lineTestReject (G : SubsetSumCode q L) {A : Type*} [AddCommMonoid A]
    (Y : (Fin r → Fin L) → A) : ℝ :=
  ((Finset.univ.filter fun α => ¬ ∀ i, G.IsCodeword (line Y α i)).card : ℝ) / (L : ℝ) ^ r

/-- `κ_r := 4 (2r)^8 δ^{−7r}`; Lemma 3.15, p.13. -/
noncomputable def kappa (δ : ℝ) (r : ℕ) : ℝ :=
  4 * (2 * (r : ℝ)) ^ 8 * (δ⁻¹) ^ (7 * r)

/-- `C^{⊗k}`: the words all of whose axis lines lie in the linear code `C`; Theorem A.2, p.32. -/
def tensorPowerCode {F : Type*} [Field F] {n : ℕ} (C : Submodule F (Fin n → F)) (k : ℕ) :
    Set ((Fin k → Fin n) → F) :=
  {w | ∀ (α : Fin k → Fin n) (i : Fin k), line w α i ∈ C}

end TimeSpaceMA


