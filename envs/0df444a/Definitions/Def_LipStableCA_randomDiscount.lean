-- Prove2me | Definitions.Def_LipStableCA_randomDiscount
-- name    : LipStableCA_randomDiscount
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T20:49:19.564883+00:00
-- url     : https://prove2.me/theorems/324296ba-8217-4cb3-b21b-a40a1b07f3ba
-- title:
--   Mechanism 2: the random discount auction
-- statement:
--   Fix $0<\epsilon<1$ and a total order on allocations. Draw $U_{i,B}\sim\mathrm{Unif}[0,1]$ independently for each bidder $i$ and nonempty bundle $B$, and set $a_{i,B}=1-\epsilon U_{i,B}^{1/m}$, with $a_{i,\emptyset}=1$. Let $S^*$ be the first allocation in the order maximizing $\sum_ia_{i,S_i}v_i(S_i)$, and let
--   $$\bar p_i=\max_{T\in\mathcal A}\sum_{h\ne i}a_{h,T_h}v_h(T_h)-\sum_{h\ne i}a_{h,S^*_h}v_h(S^*_h).$$
--   With probability $a_{i,S^*_i}$, independently across bidders, bidder $i$ gets $S^*_i$ and pays $\bar p_i/a_{i,S^*_i}$; otherwise she gets $\emptyset$ and pays $0$.
--
--   **Formalization Note.** The seed is $(U,C)$ with $C_i$ uniform on $[0,1]$, and delivery means $C_i<a_{i,S^*_i}$. The array $U$ has an ignored coordinate for $B=\emptyset$. The order is an explicit parameter.
-- source:
--   Afshinmehr, Koutsoupias, Lipschitz Stable Combinatorial Auctions, STOC 2027 submission (manuscript sha256 c5e4c53f…), Mechanism 2, p.14; §4.1.1, p.15

import Definitions.Def_LipStableCA_Mechanism

open MeasureTheory

namespace LipStableCA

variable {n m : ℕ}

/-- The uniform law on `[0, 1]`. -/
noncomputable abbrev unitLaw : Measure ℝ := volume.restrict (Set.Icc 0 1)

/-- The discount `a_{i,B} = 1 − ϵ U_{i,B}^{1/m}`, Mechanism 2, line 2, p.14, with `a_{i,∅} = 1`, line 3.
**Formalization Note.** `U` has a coordinate for `B = ∅` that is ignored. -/
noncomputable def discount (ϵ : ℝ) (U : Fin n → Finset (Fin m) → ℝ) (i : Fin n)
    (B : Finset (Fin m)) : ℝ :=
  if B = ∅ then 1 else 1 - ϵ * (U i B) ^ (1 / (m : ℝ))

/-- The law of the uniform variables `U_{i,B}`: independent, uniform on `[0, 1]`. -/
noncomputable def discountMeasure (n m : ℕ) : Measure (Fin n → Finset (Fin m) → ℝ) :=
  Measure.pi fun _ => Measure.pi fun _ => unitLaw

/-- The seed of Mechanism 2: the variables `U`, and one delivery coin `Cᵢ` per bidder. -/
abbrev DiscountSeed (n m : ℕ) := (Fin n → Finset (Fin m) → ℝ) × (Fin n → ℝ)

/-- The seed law of Mechanism 2: `U` and the coins are independent uniforms on `[0, 1]`. -/
noncomputable def discountSeedMeasure (n m : ℕ) : Measure (DiscountSeed n m) :=
  (discountMeasure n m).prod (Measure.pi fun _ => unitLaw)

/-- The discounted welfare `Σᵢ a_{i,Tᵢ} uᵢ(Tᵢ)` of Mechanism 2, line 4, p.14, for a vector of
discounts `a`. -/
noncomputable def discountedWelfare (a : Fin n → Finset (Fin m) → ℝ) (u : Profile n m)
    (T : Alloc n m) : ℝ :=
  ∑ i, a i (T.1 i) * u i (T.1 i)

/-- `S*(u, a)`, §4.1.1, p.15: the first allocation in the fixed order that maximizes the discounted
welfare at `u`. -/
noncomputable def selected (ord : LinearOrder (Alloc n m)) (a : Fin n → Finset (Fin m) → ℝ)
    (u : Profile n m) : Alloc n m :=
  firstMaximizerOn ord Finset.univ Finset.univ_nonempty (discountedWelfare a u)

/-- The discounted welfare `Σ_{h≠i} a_{h,Tₕ} vₕ(Tₕ)` of the bidders other than `i`. -/
noncomputable def othersDiscounted (a : Fin n → Finset (Fin m) → ℝ) (v : Profile n m) (i : Fin n)
    (T : Alloc n m) : ℝ :=
  ∑ h ∈ Finset.univ.erase i, a h (T.1 h) * v h (T.1 h)

/-- The expected payment `p̄ᵢ`, Mechanism 2, line 6, p.14:
`max_{T ∈ A} Σ_{h≠i} a_{h,Tₕ} vₕ(Tₕ) − Σ_{h≠i} a_{h,S*ₕ} vₕ(S*ₕ)`. -/
noncomputable def expectedPayment (ord : LinearOrder (Alloc n m)) (a : Fin n → Finset (Fin m) → ℝ)
    (v : Profile n m) (i : Fin n) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (othersDiscounted a v i) -
    othersDiscounted a v i (selected ord a v)

/-- `S*` restricted to the bidders in `D`, who keep their bundle; the others get `∅`. -/
def Alloc.restrict (T : Alloc n m) (D : Finset (Fin n)) : Alloc n m :=
  ⟨fun i => if i ∈ D then T.1 i else ∅, by
    intro i i' h
    by_cases hi : i ∈ D <;> by_cases hi' : i' ∈ D <;> simp [hi, hi', T.2 i i' h]⟩

open Classical in
/-- The bidders whose bundle is delivered, Mechanism 2, line 7, p.14: `Cᵢ < a_{i,S*ᵢ}`, an event of
probability `a_{i,S*ᵢ}` for `Cᵢ` uniform on `[0, 1]`, independently across bidders. -/
noncomputable def deliveredSet (ord : LinearOrder (Alloc n m)) (a : Fin n → Finset (Fin m) → ℝ)
    (v : Profile n m) (C : Fin n → ℝ) : Finset (Fin n) :=
  Finset.univ.filter fun i => C i < a i ((selected ord a v).1 i)

open Classical in
/-- **Mechanism 2 (Random discount auction)**, p.14, for a fixed order `ord` on `A` and a parameter
`ϵ`. On seed `(U, C)`: bidder `i` gets `S*ᵢ` and pays `p̄ᵢ / a_{i,S*ᵢ}` if `Cᵢ < a_{i,S*ᵢ}`, and otherwise
gets `∅` and pays `0`. **Formalization Note.** `ord` is the total order "fixed before the reports are
seen"; every statement about this mechanism is for every order. -/
noncomputable def randomDiscount (ord : LinearOrder (Alloc n m)) (ϵ : ℝ) :
    Mechanism n m (DiscountSeed n m) where
  alloc v ω := (selected ord (discount ϵ ω.1) v).restrict (deliveredSet ord (discount ϵ ω.1) v ω.2)
  pay v ω i :=
    if ω.2 i < discount ϵ ω.1 i ((selected ord (discount ϵ ω.1) v).1 i) then
      expectedPayment ord (discount ϵ ω.1) v i /
        discount ϵ ω.1 i ((selected ord (discount ϵ ω.1) v).1 i)
    else 0

end LipStableCA


