-- Prove2me | Definitions.Def_LipStableCA_discountIndex
-- name    : LipStableCA_discountIndex
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T20:51:00.084345+00:00
-- url     : https://prove2.me/theorems/644215e5-88e8-4070-92bc-c678fb2749e1
-- title:
--   The scores and indices of §4.1.1
-- statement:
--   Fix a bidder $i$, the reports of the others, and a zero pattern $\mathcal B$. For a vector of discounts $a$, $c_B(a)=\max\{\sum_{h\ne i}a_{h,T_h}v_h(T_h):T_i=B\}$ is the best discounted welfare of the other bidders when $i$ gets $B$, and $c_0(a)=\max_{B\notin\mathcal B}c_B(a)$. An allocation $T$ has index $B\in\mathcal B$ if $T_i=B$, and index $0$ if $T_i\notin\mathcal B$. The scores at a profile $u$ are $s_0(u,a)=c_0(a)$ and $s_B(u,a)=c_B(a)+a_{i,B}u_i(B)$. $J(u,a)$ is the index of the selected allocation $S^*(u,a)$. $U$ is the set of valid profiles agreeing with $v$ off $i$ with zero pattern $\mathcal B$ at $i$.
--
--   **Formalization Note.** The paper's enumeration $B_1,\dots,B_R$ is replaced by the bundles themselves.
-- source:
--   Afshinmehr, Koutsoupias, Lipschitz Stable Combinatorial Auctions, STOC 2027 submission (manuscript sha256 c5e4c53f…), §4.1.1, p.16

import Definitions.Def_LipStableCA_randomDiscount

namespace LipStableCA

variable {n m : ℕ}

/-- The allocation with bundle `B` for bidder `i` and `∅` for the others. -/
def Alloc.single (i : Fin n) (B : Finset (Fin m)) : Alloc n m :=
  ⟨fun h => if h = i then B else ∅, by
    intro h h' hne
    by_cases h1 : h = i <;> by_cases h2 : h' = i
    · exact absurd (h1.trans h2.symm) hne
    · simp [h1, h2]
    · simp [h1, h2]
    · simp [h1, h2]⟩

open Classical in
/-- `c_B(a) = max{Σ_{h≠i} a_{h,Tₕ} vₕ(Tₕ) : T ∈ A, Tᵢ = B}`, §4.1.1, p.16. -/
noncomputable def cBundle (a : Fin n → Finset (Fin m) → ℝ) (v : Profile n m) (i : Fin n)
    (B : Finset (Fin m)) : ℝ :=
  (Finset.univ.filter fun T : Alloc n m => T.1 i = B).sup'
    ⟨Alloc.single i B, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
      show (if i = i then B else ∅) = B
      simp⟩⟩ (othersDiscounted a v i)

open Classical in
/-- `𝓑`, §4.1.1, p.16: the bundles of positive value for bidder `i`, the zero pattern of `vᵢ`. The paper
enumerates it as `B₁, …, B_R`. -/
noncomputable def positiveBundles (u : Finset (Fin m) → ℝ) : Finset (Finset (Fin m)) :=
  Finset.univ.filter fun B => 0 < u B

/-- The index set `{0, 1, …, R}` of §4.1.1, p.16. **Formalization Note.** Index `j ∈ [R]` is the bundle
`Bⱼ ∈ 𝓑` itself, written `some Bⱼ`, and index `0` is `none`. The enumeration plays no role in the paper. -/
abbrev BundleIndex (m : ℕ) := Option (Finset (Fin m))

/-- `k` is an index of `{0, 1, …, R}`: `none`, or `some B` with `B ∈ 𝓑`. -/
def IsIndex (𝓑 : Finset (Finset (Fin m))) (k : BundleIndex m) : Prop :=
  ∀ B, k = some B → B ∈ 𝓑

open Classical in
/-- `c₀(a) = max_{B ∉ 𝓑} c_B(a)`, p.16. **Formalization Note.** `∅` is inserted so the maximum ranges
over a nonempty set; `∅ ∉ 𝓑` on valid zero patterns, so it changes nothing. -/
noncomputable def cZero (a : Fin n → Finset (Fin m) → ℝ) (v : Profile n m) (i : Fin n)
    (𝓑 : Finset (Finset (Fin m))) : ℝ :=
  (insert ∅ 𝓑ᶜ).sup' ⟨∅, Finset.mem_insert_self _ _⟩ (cBundle a v i)

/-- `c_k(a)` for an index `k`: `c₀(a)` at index `0`, and `c_{B}(a)` at the index of `B`, p.16. -/
noncomputable def cIndex (a : Fin n → Finset (Fin m) → ℝ) (v : Profile n m) (i : Fin n)
    (𝓑 : Finset (Finset (Fin m))) : BundleIndex m → ℝ
  | none => cZero a v i 𝓑
  | some B => cBundle a v i B

/-- The score of an index at the profile `u`, p.16: `s₀(u, a) = c₀(a)` and
`sⱼ(u, a) = cⱼ(a) + aⱼ uᵢ(Bⱼ)`. -/
noncomputable def score (a : Fin n → Finset (Fin m) → ℝ) (v : Profile n m) (i : Fin n)
    (𝓑 : Finset (Finset (Fin m))) (u : Profile n m) : BundleIndex m → ℝ
  | none => cZero a v i 𝓑
  | some B => cBundle a v i B + a i B * u i B

open Classical in
/-- The index of an allocation, p.16: `Bⱼ` if `Tᵢ = Bⱼ`, and `0` if `Tᵢ ∉ 𝓑`. -/
noncomputable def allocIndex (i : Fin n) (𝓑 : Finset (Finset (Fin m))) (T : Alloc n m) :
    BundleIndex m :=
  if T.1 i ∈ 𝓑 then some (T.1 i) else none

/-- `T` attains `c_k(a)`, p.16: `Σ_{h≠i} a_{h,Tₕ} vₕ(Tₕ) = c_k(a)`. -/
def Attains (a : Fin n → Finset (Fin m) → ℝ) (v : Profile n m) (i : Fin n)
    (𝓑 : Finset (Finset (Fin m))) (T : Alloc n m) (k : BundleIndex m) : Prop :=
  othersDiscounted a v i T = cIndex a v i 𝓑 k

/-- The set `U` of §4.1.1, p.16: profiles `u` with `u₋ᵢ = v₋ᵢ` in which bidder `i` has the zero pattern
`𝓑`. -/
def InPattern (v : Profile n m) (i : Fin n) (𝓑 : Finset (Finset (Fin m))) (u : Profile n m) : Prop :=
  IsProfile u ∧ (∀ h, h ≠ i → u h = v h) ∧ ∀ B, 0 < u i B ↔ B ∈ 𝓑

/-- `J(u, a)`, p.16: the index of `S*(u, a)`. -/
noncomputable def selectedIndex (ord : LinearOrder (Alloc n m)) (i : Fin n)
    (𝓑 : Finset (Finset (Fin m))) (a : Fin n → Finset (Fin m) → ℝ) (u : Profile n m) :
    BundleIndex m :=
  allocIndex i 𝓑 (selected ord a u)

end LipStableCA


