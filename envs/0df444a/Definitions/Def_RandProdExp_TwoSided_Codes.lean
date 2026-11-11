-- Prove2me | Definitions.Def_RandProdExp_TwoSided_Codes
-- name    : RandProdExp_TwoSided_Codes
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T20:18:36.457675+00:00
-- url     : https://prove2.me/theorems/2f20be4a-4ca7-4995-8aa8-bc00e919127b
-- title:
--   Codes on $[n]^D$: $C^{(i)}$, tensor and check-product codes, line codes, two-sided $\nu$-product expansion, extendability, inner-generation, $\pi_M$, $\tau_M$, random codes (Defs. 3.15–3.20, §4)
-- statement:
--   Let $K$ be a field and $C_1,\dots,C_D\subseteq K^n$ linear codes. A word on the grid is a function $x:[n]^D\to K$; its restriction $x|_\ell\in K^n$ to an $i$-parallel line $\ell$ is read along the $i$-th coordinate.
--
--   * $C^{(i)}=K^n\otimes\cdots\otimes C_i\otimes\cdots\otimes K^n$ is the set of words whose restriction to every $i$-parallel line lies in $C_i$; the **tensor code** is $\bigotimes_iC_i=\bigcap_iC^{(i)}$ and the **check-product code** is $\boxplus_iC_i=\sum_iC^{(i)}$ (Definition 3.16).
--   * For an $i$-parallel line $\ell$, $C_\ell=\{c:\operatorname{supp}(c)\subseteq\ell,\ c|_\ell\in C_i\}$ (Definition 3.15).
--   * $|x|$ is the Hamming weight and $|a|_i$ the number of $i$-parallel lines on which $a$ is not identically zero. The tuple $(C_i)$ is **$\nu$-product expanding** (Definition 3.20) if every $x\in\boxplus_iC_i$ has a decomposition $x=\sum_ia_i$, $a_i\in C^{(i)}$, with
--   $$\nu\, n\sum_{i=1}^D|a_i|_i\le|x| .$$
--   It is **two-sided $\nu$-product expanding** if both $(C_i)$ and $(C_i^\perp)$ are, duals taken for the standard dot product on $K^n$ (the published `GoodQLTC_dualCode`).
--   * $F_C(M)$ is the set of words on $M$ whose restriction to every axis-parallel line $\ell\subseteq M$ of direction $i$ lies in $C_i$ (Definition 3.17); $M$ is **extendable** in $C=\bigotimes_iC_i$ if every word of $F(M)$ is the restriction to $M$ of a codeword of $C$, i.e. the restriction map $\pi_M:C\to F(M)$ is surjective (Definition 3.18).
--   * $M$ is **inner-generated** for $\boxplus_iC_i$ if every $c\in\boxplus_iC_i$ with $\operatorname{supp}(c)\subseteq M$ lies in $\sum_{\ell\in L(M)}C_\ell$ (Definition 3.19).
--   * With $B_i=C_i^\perp$ and $B=\boxplus_iB_i$, the **global corestriction map** of $(C_i)$ is
--   $$\tau_M:\ K^M\Big/\sum_{\ell\in L(M)}B_\ell\ \longrightarrow\ K^{[n]^D}\big/B,$$
--   induced by extension by zero (§4.2, Equation (11), Fact 4.4).
--   * $\mathrm{Gr}(n,k)$ is the set of $k$-dimensional subspaces of $K^n$ ($\mathrm{Gr}_{p^t}(n,k)$ over $\mathbb F_{p^t}$); for a finite field, independent uniformly random codes $C_i\in\mathrm{Gr}(n,k_i)$ means the uniform counting probability on $\prod_i\mathrm{Gr}(n,k_i)$.
--
--   These are the objects of the goal (two-sided product expansion of uniformly random codes) and of the duality between extendability and inner-generatedness that reduces it to the injectivity of $\tau_M$.
--
--   **Formalization Note** $K^n$ is `Fin n → K` and grid words are `(Fin D → Fin n) → K`. $K^M$ is encoded as the words vanishing outside $M$ (`supported M`), which extension by zero identifies with $K^M$; $F(M)$, $\pi_M$ (`restrictionMap`, $c\mapsto$ the word equal to $c$ on $M$ and $0$ outside) and $\tau_M$ (`tauMap`, built with `Submodule.mapQ` from the inclusion of `supported M`) use this encoding. `tauMap M C` takes the tuple $(C_i)$ and forms $B_i=C_i^\perp$ itself. No sign condition is put on $\nu$. `codeProb` is a ratio of `Nat.card`s; all sets involved are finite over a finite field.
-- source:
--   Chattopadhyay, Ringach, Spooner, Product Expansion of Random Codes via Analytic Techniques, STOC 2027 submission (manuscript sha256 9e4ac2d1…), p. 1; pp. 23–24, Definitions 3.15–3.20; pp. 26–29, §4.1–4.2 (π_M, Fact 4.2, Eq. (11), Fact 4.4)

import Mathlib
import Definitions.Def_GoodQLTC_dualCode
import Definitions.Def_RandProdExp_TwoSided_Grid

namespace RandProdExp.TwoSided

/-!
# Codes on the grid `[n]^D`: `C^(i)`, tensor and check-product codes, line codes, product expansion,
# extendability, inner-generatedness, the restriction map `π_M`, the corestriction map `τ_M`, and
# uniformly random codes

Chattopadhyay, Ringach, Spooner, *Product Expansion of Random Codes via Analytic Techniques*,
STOC 2027 submission, §1 p. 1, §3.4 pp. 23–24 (Definitions 3.15–3.20), §4.1–4.2 pp. 26–29
(the restriction map `π_M`, Fact 4.2; the corestriction map `τ_M`, Equation (11) and Fact 4.4).

A code is a `K`-linear subspace of `K^n = (Fin n → K)`; a word on the grid is a function
`(Fin D → Fin n) → K`. The dual code is the published `GoodQLTC.dualCode` (standard dot product).
The space `K^M` of words on `M ⊆ [n]^D` is encoded as the words on the grid that vanish outside `M`
(extension by zero `ι_M` is a linear isomorphism onto this subspace).
-/

variable {K : Type} [Field K] {D n : ℕ}

/-- The restriction `x|_ℓ ∈ K^n` of a grid word `w` to the `i`-parallel line through `x`, identified
with `[n]` via its `i`-th coordinate (§3.4, p. 23). -/
def restrictLine (w : (Fin D → Fin n) → K) (i : Fin D) (x : Fin D → Fin n) : Fin n → K :=
  fun t => w (Function.update x i t)

/-- `C^(i) = K^n ⊗ ⋯ ⊗ C_i ⊗ ⋯ ⊗ K^n`: the grid words whose restriction to every `i`-parallel line
lies in `C_i` (§1 p. 1, §3.4 p. 23). -/
def axisCode (C : Submodule K (Fin n → K)) (i : Fin D) : Submodule K ((Fin D → Fin n) → K) where
  carrier := {w | ∀ x, restrictLine w i x ∈ C}
  add_mem' := by
    intro a b ha hb x
    exact C.add_mem (ha x) (hb x)
  zero_mem' := by
    intro x
    exact C.zero_mem
  smul_mem' := by
    intro c a ha x
    exact C.smul_mem c (ha x)

/-- The tensor code `C_1 ⊗ ⋯ ⊗ C_D = ⋂_i C^(i)`. -/
def tensorCode (C : Fin D → Submodule K (Fin n → K)) : Submodule K ((Fin D → Fin n) → K) :=
  ⨅ i, axisCode (C i) i

/-- The check-product code `C_1 ⊞ ⋯ ⊞ C_D = Σ_i C^(i)` (Definition 3.16). -/
def checkProduct (C : Fin D → Submodule K (Fin n → K)) : Submodule K ((Fin D → Fin n) → K) :=
  ⨆ i, axisCode (C i) i

/-- The code along a line `C_ℓ = {c : supp(c) ⊆ ℓ, c|_ℓ ∈ C_i}` for the `i`-parallel line `ℓ` through
`x` (Definition 3.15). -/
def lineCode (C : Submodule K (Fin n → K)) (i : Fin D) (x : Fin D → Fin n) :
    Submodule K ((Fin D → Fin n) → K) where
  carrier := {c | (∀ y, y ∉ axisLine i x → c y = 0) ∧ restrictLine c i x ∈ C}
  add_mem' := by
    intro a b ha hb
    refine ⟨fun y hy => ?_, C.add_mem ha.2 hb.2⟩
    simp [ha.1 y hy, hb.1 y hy]
  zero_mem' := ⟨fun _ _ => rfl, C.zero_mem⟩
  smul_mem' := by
    intro c a ha
    refine ⟨fun y hy => ?_, C.smul_mem c ha.2⟩
    simp [ha.1 y hy]

/-- `Σ_{ℓ ∈ L(M)} C_ℓ`: the span of the line codes of all axis-parallel lines contained in `M`
(Definition 3.19). -/
def lineSum (M : Set (Fin D → Fin n)) (C : Fin D → Submodule K (Fin n → K)) :
    Submodule K ((Fin D → Fin n) → K) :=
  ⨆ (i : Fin D) (x : Fin D → Fin n) (_ : axisLine i x ⊆ M), lineCode (C i) i x

/-- A line code is contained in the corresponding `C^(i)`. -/
theorem lineCode_le_axisCode (C : Submodule K (Fin n → K)) (i : Fin D) (x : Fin D → Fin n) :
    lineCode C i x ≤ axisCode C i := by
  intro c hc y
  by_cases h : ∀ k, k ≠ i → y k = x k
  · have hfun : restrictLine c i y = restrictLine c i x := by
      funext t
      unfold restrictLine
      congr 1
      funext k
      by_cases hk : k = i
      · subst hk; simp
      · simp [Function.update_of_ne hk, h k hk]
    rw [hfun]
    exact hc.2
  · push Not at h
    obtain ⟨k, hki, hk⟩ := h
    have hzero : restrictLine c i y = 0 := by
      funext t
      apply hc.1
      intro hmem
      apply hk
      have := hmem k hki
      simpa [Function.update_of_ne hki] using this
    rw [hzero]
    exact C.zero_mem

/-- `Σ_{ℓ ∈ L(M)} C_ℓ ⊆ C_1 ⊞ ⋯ ⊞ C_D`. -/
theorem lineSum_le_checkProduct (M : Set (Fin D → Fin n)) (C : Fin D → Submodule K (Fin n → K)) :
    lineSum M C ≤ checkProduct C := by
  unfold lineSum checkProduct
  refine iSup_le fun i => iSup_le fun x => iSup_le fun _ => ?_
  exact (lineCode_le_axisCode (C i) i x).trans (le_iSup (fun i => axisCode (C i) i) i)

/-- The Hamming weight `|x|` of a grid word. -/
noncomputable def hammingWeight (w : (Fin D → Fin n) → K) : ℕ :=
  {y | w y ≠ 0}.ncard

/-- `|a|_i`: the number of `i`-parallel lines on which the word `a` does not vanish (p. 24). -/
noncomputable def lineWeight (w : (Fin D → Fin n) → K) (i : Fin D) : ℕ :=
  {ℓ : Set (Fin D → Fin n) | ∃ x, ℓ = axisLine i x ∧ ∃ y ∈ ℓ, w y ≠ 0}.ncard

/-- **ν-product expansion** (Definition 3.20): every `x ∈ ⊞_i C_i` admits a decomposition
`x = Σ_i a_i` with `a_i ∈ C^(i)` and `ν n Σ_i |a_i|_i ≤ |x|`. No sign condition on `ν` is imposed. -/
def IsProductExpanding (ν : ℝ) (C : Fin D → Submodule K (Fin n → K)) : Prop :=
  ∀ x ∈ checkProduct C, ∃ a : Fin D → ((Fin D → Fin n) → K),
    (∀ i, a i ∈ axisCode (C i) i) ∧ x = ∑ i, a i ∧
    ν * n * ∑ i, (lineWeight (a i) i : ℝ) ≤ hammingWeight x

/-- **Two-sided ν-product expansion** (Definition 3.20): both `(C_i)` and `(C_i^⊥)` are ν-product
expanding, duals for the standard dot product on `K^n`. -/
def IsTwoSidedProductExpanding (ν : ℝ) (C : Fin D → Submodule K (Fin n → K)) : Prop :=
  IsProductExpanding ν C ∧ IsProductExpanding ν (fun i => GoodQLTC.dualCode (C i))

/-- The words supported in `M` (encoding of `K^M` via extension by zero). -/
def supported (M : Set (Fin D → Fin n)) : Submodule K ((Fin D → Fin n) → K) where
  carrier := {z | ∀ y, y ∉ M → z y = 0}
  add_mem' := by
    intro a b ha hb y hy
    simp [ha y hy, hb y hy]
  zero_mem' := fun _ _ => rfl
  smul_mem' := by
    intro c a ha y hy
    simp [ha y hy]

/-- `F_C(M)` (Definition 3.17): the words on `M` (supported in `M`) whose restriction to every
axis-parallel line `ℓ ⊆ M` of direction `i` lies in `C_i`. -/
def localWords (M : Set (Fin D → Fin n)) (C : Fin D → Submodule K (Fin n → K)) :
    Submodule K ((Fin D → Fin n) → K) where
  carrier := {z | (∀ y, y ∉ M → z y = 0) ∧
    ∀ (i : Fin D) (x : Fin D → Fin n), axisLine i x ⊆ M → restrictLine z i x ∈ C i}
  add_mem' := by
    intro a b ha hb
    refine ⟨fun y hy => ?_, fun i x hx => (C i).add_mem (ha.2 i x hx) (hb.2 i x hx)⟩
    simp [ha.1 y hy, hb.1 y hy]
  zero_mem' := ⟨fun _ _ => rfl, fun i _ _ => (C i).zero_mem⟩
  smul_mem' := by
    intro c a ha
    refine ⟨fun y hy => ?_, fun i x hx => (C i).smul_mem c (ha.2 i x hx)⟩
    simp [ha.1 y hy]

/-- **Extendability** (Definition 3.18): every local word in `F(M)` is the restriction to `M` of a
codeword of the tensor code `C = C_1 ⊗ ⋯ ⊗ C_D`. -/
def Extendable (M : Set (Fin D → Fin n)) (C : Fin D → Submodule K (Fin n → K)) : Prop :=
  ∀ f ∈ localWords M C, ∃ c ∈ tensorCode C, ∀ y ∈ M, c y = f y

open Classical in
/-- The restriction map `π_M : C → F(M)`, `c ↦ c|_M` (Definition 3.18, §4.1 p. 27), with `c|_M`
encoded as the word equal to `c` on `M` and `0` outside. -/
noncomputable def restrictionMap (M : Set (Fin D → Fin n)) (C : Fin D → Submodule K (Fin n → K)) :
    tensorCode C →ₗ[K] localWords M C where
  toFun c := ⟨M.indicator c.1, by
    refine ⟨fun y hy => Set.indicator_of_notMem hy _, fun i x hx => ?_⟩
    have hc : c.1 ∈ axisCode (C i) i := (Submodule.mem_iInf _).1 c.2 i
    have hfun : restrictLine (M.indicator c.1) i x = restrictLine c.1 i x := by
      funext t
      unfold restrictLine
      apply Set.indicator_of_mem
      apply hx
      intro k hk
      simp [Function.update_of_ne hk]
    rw [hfun]
    exact hc x⟩
  map_add' := by
    intro a b
    ext y
    simp only [Submodule.coe_add, Pi.add_apply, Set.indicator_apply]
    split_ifs <;> simp
  map_smul' := by
    intro c a
    ext y
    simp only [Submodule.coe_smul, Pi.smul_apply, Set.indicator_apply, RingHom.id_apply]
    split_ifs <;> simp

/-- **Inner-generated** (Definition 3.19): every codeword of `C_1 ⊞ ⋯ ⊞ C_D` supported in `M` lies in
`Σ_{ℓ ∈ L(M)} C_ℓ`. -/
def InnerGenerated (M : Set (Fin D → Fin n)) (C : Fin D → Submodule K (Fin n → K)) : Prop :=
  ∀ c ∈ checkProduct C, (∀ y, y ∉ M → c y = 0) → c ∈ lineSum M C

/-- The **global corestriction map** of the tuple `(C_i)` (§4.2, Equation (11), Fact 4.4): with
`B_i = C_i^⊥` and `B = B_1 ⊞ ⋯ ⊞ B_D`,
`τ_M : K^M / Σ_{ℓ ∈ L(M)} B_ℓ → K^{[n]^D} / B` is the map induced by extension by zero. -/
noncomputable def tauMap (M : Set (Fin D → Fin n)) (C : Fin D → Submodule K (Fin n → K)) :
    (supported (K := K) M ⧸
        (lineSum M (fun i => GoodQLTC.dualCode (C i))).comap (supported M).subtype) →ₗ[K]
      (((Fin D → Fin n) → K) ⧸ checkProduct (fun i => GoodQLTC.dualCode (C i))) :=
  Submodule.mapQ _ _ (supported M).subtype
    (Submodule.comap_mono (lineSum_le_checkProduct M (fun i => GoodQLTC.dualCode (C i))))

/-- The Grassmannian `Gr(n, k)` of `k`-dimensional subspaces of `K^n` (§3.4, p. 24); over
`K = 𝔽_{p^t}` this is `Gr_{p^t}(n, k)`. -/
def Grass (K : Type) [Field K] (n k : ℕ) : Type :=
  {C : Submodule K (Fin n → K) // Module.finrank K C = k}

/-- The probability of an event `E` for independent uniformly random codes `C_i ∈ Gr(n, k_i)`,
`i ∈ [D]`: the uniform counting probability on the finite product `∏_i Gr(n, k_i)` (for a finite
field `K`). -/
noncomputable def codeProb (K : Type) [Field K] {D : ℕ} (n : ℕ) (k : Fin D → ℕ)
    (E : ((i : Fin D) → Grass K n (k i)) → Prop) : ℝ :=
  (Nat.card {C : (i : Fin D) → Grass K n (k i) // E C} : ℝ) /
    (Nat.card ((i : Fin D) → Grass K n (k i)) : ℝ)

end RandProdExp.TwoSided


