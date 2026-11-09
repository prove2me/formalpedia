-- Prove2me | Definitions.Def_FluidGreedyMatching_CliqueBomb_DoubleBomb
-- name    : FluidGreedyMatching_CliqueBomb_DoubleBomb
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:57:34.63582+00:00
-- url     : https://prove2.me/theorems/475e126d-bf86-44c0-b461-c9ab08bc832b
-- title:
--   Double-Bomb graphs, eight counters and fluid equations
-- statement:
--   For $n\ge1$, $\sigma>0$ and $\kappa\in\{0,1\}$, let $m=\lfloor\sigma n\rfloor$. The disjoint classes $X,Y,X',Y'$ have size $n$ and $P,Q$ have size $m$. Include the paired edges $x_ix'_i,y_iy'_i,p_jq_j$; the complete joins $X$–$Y$, $X$–$P$, $Y$–$Q$; and, precisely when $\kappa=1$, the two hub cliques. There are no other edges. The representation is a disjoint sum of labeled finite classes; a Boolean flag represents the two values of $\kappa$.
--
--   For a run state, the eight coordinates are $(H_X,H_Y,W_X,W_Y,N_{11},N_{10},N_{01},|M_t|)$. The $H$ coordinates count active hubs and $W$ counts every active antenna, including isolated ones. The three satellite counts count intact pairs, only their $P$ endpoint, and only their $Q$ endpoint. The active-mass linear map is
--   $$u(z)=h_X+h_Y+w_X+w_Y+2n_{11}+n_{10}+n_{01}.$$
--   Output deviation probabilities and expected ratios use the actual finite MRG law at size $n+1$.
--
--   Writing $\eta=(1+\kappa)h+q$, the log-time fluid equation is
--   $$h'=-h\left(2+\frac{(1+\kappa)h}{\eta}\right)-q,\qquad q'=-q\left(1+\frac h\eta\right),\qquad h(0)=1,\ q(0)=\sigma.$$
--   A first-exhaustion solution is continuous up to a finite endpoint $S>0$, satisfies these equations before $S$, has $h,q>0$ before $S$, and has $h(S)=0$. Existence of such a solution is a theorem conclusion. Its matching value is $\int_0^S(4h+2q)\,ds+q(S)^2/\sigma$. These definitions distinguish actual asymmetric counts from a symmetric deterministic trajectory.
-- source:
--   Sayan Mukherjee, Fluid Limits and Upper Bounds for Randomized Greedy Matching, STOC 2027 submission #492 (October 2026), Definition 2.2, p. 8; Section 4.2, p. 14; Table 3, p. 21; Eq. (5.1) and Lemma 5.1, pp. 22–24

import Mathlib
import Definitions.Def_FluidGreedyMatching_CliqueBomb_ProcessModel

set_option autoImplicit false

namespace FluidGreedyMatching.CliqueBomb

noncomputable section

/-- Hub/antenna classes 0=X, 1=Y, 2=X', 3=Y'; satellite classes 0=P, 1=Q. -/
abbrev BombVertex (n m : ℕ) := (Fin 4 × Fin n) ⊕ (Fin 2 × Fin m)

def satellites (σ : ℝ) (n : ℕ) : ℕ := ⌊σ * (n : ℝ)⌋₊

/-- Directed generators of the edges; symmetrized below. -/
def bombEdge (κ : Bool) {n m : ℕ} : BombVertex n m → BombVertex n m → Prop
  | .inl (c, i), .inl (d, j) =>
      (c = 0 ∧ d = 2 ∧ i = j) ∨ (c = 1 ∧ d = 3 ∧ i = j) ∨
      (c = 0 ∧ d = 1) ∨ (κ = true ∧ c = d ∧ (c = 0 ∨ c = 1))
  | .inl (c, _), .inr (d, _) => (c = 0 ∧ d = 0) ∨ (c = 1 ∧ d = 1)
  | .inr (c, i), .inr (d, j) => c = 0 ∧ d = 1 ∧ i = j
  | .inr _, .inl _ => False

/-- The exact finite graph, with floor counts, sparse paired edges, complete joins,
and optional hub cliques. No transition or limit approximation is used here. -/
def doubleBomb (σ : ℝ) (κ : Bool) (n : ℕ) :
    SimpleGraph (BombVertex n (satellites σ n)) where
  Adj v w := v ≠ w ∧ (bombEdge κ v w ∨ bombEdge κ w v)
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- Counts of all active members of a named hub/antenna class. -/
def hubClassCount {n m : ℕ} (U : Finset (BombVertex n m)) (c : Fin 4) : ℕ := by
  classical
  exact (Finset.univ.filter (fun i : Fin n => Sum.inl (c, i) ∈ U)).card

/-- Satellite-pair state (both, only P, only Q). -/
def pairCount {n m : ℕ} (U : Finset (BombVertex n m)) (p q : Bool) : ℕ := by
  classical
  exact (Finset.univ.filter (fun j : Fin m =>
    (Sum.inr ((0 : Fin 2), j) ∈ U ↔ p = true) ∧
    (Sum.inr ((1 : Fin 2), j) ∈ U ↔ q = true))).card

/-- Table 3 count vector (HX,HY,WX,WY,N11,N10,N01,|Mt|).
Antennas are counted even when isolated; opposite sides are never identified. -/
def bombCounts {n m : ℕ} (S : RunState (BombVertex n m)) : Vec 8 :=
  ![(hubClassCount S.1 0 : ℝ), (hubClassCount S.1 1 : ℝ),
    (hubClassCount S.1 2 : ℝ), (hubClassCount S.1 3 : ℝ),
    (pairCount S.1 true true : ℝ), (pairCount S.1 true false : ℝ),
    (pairCount S.1 false true : ℝ), (S.2.card : ℝ)]

/-- Linear active mass, including two endpoints for each intact satellite pair. -/
def activeMass : Vec 8 →ₗ[ℝ] ℝ where
  toFun z := z 0 + z 1 + z 2 + z 3 + 2 * z 4 + z 5 + z 6
  map_add' := by intro x y; simp only [Pi.add_apply]; ring
  map_smul' := by intro c z; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

/-- Exact output-law tail probability, a finite sum over actual MRG matchings. -/
def bombDeviation (σ : ℝ) (κ : Bool) (n : ℕ) (L δ : ℝ) : ℝ := by
  classical
  let G := doubleBomb σ κ (n + 1)
  exact ∑ M : Finset (Sym2 (BombVertex (n + 1) (satellites σ (n + 1)))),
    if δ < |(M.card : ℝ) / scale n - L| then ((outputLaw G) M).toReal else 0

def bombRatio (σ : ℝ) (κ : Bool) (n : ℕ) : ℝ :=
  expectedRatio (doubleBomb σ κ (n + 1))

/-- Eq. (5.1)'s right hand side in log-time. σ specifies initial data, not the drift. -/
def fluidDrift (κ : Bool) (h q : ℝ) : ℝ × ℝ :=
  let k : ℝ := if κ then 1 else 0
  let η := (1 + k) * h + q
  (-h * (2 + (1 + k) * h / η) - q, -q * (1 + h / η))

/-- A solution up to the first hub exhaustion, with continuous endpoint values.
The existence of this data and positivity of its endpoint are theorem conclusions. -/
def isFluidSolution (σ : ℝ) (κ : Bool) (S : ℝ) (h q : ℝ → ℝ) : Prop :=
  0 < S ∧ h 0 = 1 ∧ q 0 = σ ∧
  ContinuousOn h (Set.Icc 0 S) ∧ ContinuousOn q (Set.Icc 0 S) ∧
  h S = 0 ∧ (∀ s ∈ Set.Ico 0 S, 0 < h s ∧ 0 < q s ∧
    HasDerivWithinAt h (fluidDrift κ (h s) (q s)).1 (Set.Ici 0) s ∧
    HasDerivWithinAt q (fluidDrift κ (h s) (q s)).2 (Set.Ici 0) s)

/-- The full edge contribution, including the surviving satellite pairs. -/
def fluidValue (σ S : ℝ) (h q : ℝ → ℝ) : ℝ :=
  (∫ s in (0 : ℝ)..S, (4 * h s + 2 * q s)) + (q S)^2 / σ

end
end FluidGreedyMatching.CliqueBomb


