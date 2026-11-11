-- Prove2me | Definitions.Def_EntAssistOneWay_Separation_GroupProblems
-- name    : EntAssistOneWay_Separation_GroupProblems
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T20:44:14.188367+00:00
-- url     : https://prove2.me/theorems/2df2908c-52c0-4429-86a3-f0aff40b1597
-- title:
--   Bounded subgroup membership, shifted equality, and representation gaps
-- statement:
--   For a finite group $G$, write $\mathcal H_{G,k}=\{H\le G:|H|\le k\}$. Bounded-order membership returns one exactly when Bob's group element belongs to Alice's subgroup. Write $S=\mathbb F_2^r$. Shifted equality is the total function
--   $$\operatorname{ShiftEq}_{G,r}((g_1,g_2),(h,s))=1\quad\Longleftrightarrow\quad\forall x\in S,\ g_1(x)g_2(x+s)=h(x).$$
--   Translations of arrays define automorphisms and a homomorphism from the multiplicative copy of the additive shift group. A central order-three element is an element $\zeta\in Z(G)$ with $\operatorname{ord}(\zeta)=3$. The dimension-gap predicate for $D\ge1$ requires every complex representation of dimension $d<D$ to send $\zeta$ to the identity. A common phase $\phi\in\mathbb F_3$ rotates every coordinate by $\zeta^{\phi}$. The matrix of Lemma 5.7 has entry $1[x\cdot y=0]$ in $\mathbb F_3$.
--
--   These definitions share one group convention throughout §§4–6. The dimension-gap predicate does not assert minimality, existence of a nontrivial representation, or the lower-bound conclusion itself.
-- source:
--   Ryan Anselm, Srijita Kundu, Olivier Lalonde, Ashwin Nayak, STOC 2027 submission #228 (October 2026), p. 13, Lemma 2.4; p. 20, Definition 4.1; pp. 24–26, Definition 5.1 and Theorem 5.2; p. 31, Lemma 5.7

import Definitions.Def_EntAssistOneWay_Separation_Analysis

open scoped BigOperators ComplexOrder
open Classical
set_option autoImplicit false

namespace EntAssistOneWay.Separation

noncomputable section

abbrev ShiftSpace (r : ℕ) := Fin r → ZMod 2
abbrev ShiftAlice (G : Type) (r : ℕ) :=
  (ShiftSpace r → G) × (ShiftSpace r → G)
abbrev ShiftBob (G : Type) (r : ℕ) := (ShiftSpace r → G) × ShiftSpace r

/-- Alice's legal subgroup inputs, with their actual cardinality bound. -/
def SmallSubgroup (G : Type) [Group G] (k : ℕ) :=
  {H : Subgroup G // Nat.card H ≤ k}

instance smallSubgroupFintype (G : Type) [Group G] [Fintype G] (k : ℕ) :
    Fintype (SmallSubgroup G k) := by
  unfold SmallSubgroup
  exact Fintype.ofFinite _

/-- Definition 4.1. -/
def membership (G : Type) [Group G] (k : ℕ) (H : SmallSubgroup G k) (g : G) : Bool :=
  decide (g ∈ H.val)

/-- Definition 5.1; no promise restricts the no-instances. -/
def shiftEq {G : Type} [Group G] (r : ℕ) (a : ShiftAlice G r) (b : ShiftBob G r) : Bool :=
  decide (∀ x, a.1 x * a.2 (x + b.2) = b.1 x)

/-- Translation, as an automorphism of the array group (Lemma 2.4). -/
def shiftAut {G S : Type} [Group G] [AddCommGroup S] (s : S) : MulAut (S → G) where
  toFun f t := f (t + s)
  invFun f t := f (t - s)
  left_inv f := by funext t; simp
  right_inv f := by funext t; simp
  map_mul' f g := rfl

/-- The action homomorphism used to form the semidirect product. -/
def shiftAction (G S : Type) [Group G] [AddCommGroup S] :
    Multiplicative S →* MulAut (S → G) where
  toFun s := shiftAut s.toAdd
  map_one' := by ext f t; simp [shiftAut]
  map_mul' s t := by ext f u; simp [shiftAut, add_comm, add_left_comm]

/-- Hypothesis-form D from Theorem 5.2, without a minimality requirement. -/
def DimensionGap {G : Type} [Group G] (ζ : G) (D : ℕ) : Prop :=
  1 ≤ D ∧ ∀ d : ℕ, d < D →
    ∀ ρ : G →* Matrix.GeneralLinearGroup (Fin d) ℂ, ρ ζ = 1

/-- Standing central order-three assumption of §5.2. -/
def CentralThree {G : Type} [Group G] (ζ : G) : Prop :=
  ζ ∈ Subgroup.center G ∧ orderOf ζ = 3

/-- Rotate every array coordinate by one common central phase. -/
def phaseArray {G : Type} [Group G] {r : ℕ}
    (ζ : G) (φ : ZMod 3) (h : ShiftSpace r → G) : ShiftSpace r → G :=
  fun x => ζ ^ φ.val * h x

/-- The shifted coordinatewise product. -/
def shiftedProduct {G : Type} [Group G] {r : ℕ}
    (g₁ g₂ : ShiftSpace r → G) (s : ShiftSpace r) : ShiftSpace r → G :=
  fun x => g₁ x * g₂ (x + s)

/-- The F₃ matrix of Lemma 5.7. -/
def dotIndicator (r : ℕ) : Matrix (ShiftSpace r) (ShiftSpace r) (ZMod 3) :=
  fun x y => if ∑ i, x i * y i = 0 then 1 else 0

end

end EntAssistOneWay.Separation


