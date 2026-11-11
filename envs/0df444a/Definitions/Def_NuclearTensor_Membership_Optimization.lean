-- Prove2me | Definitions.Def_NuclearTensor_Membership_Optimization
-- name    : NuclearTensor_Membership_Optimization
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T22:17:11.634866+00:00
-- url     : https://prove2.me/theorems/a6d39e80-5907-41ec-a8f6-6b3d1160713c
-- title:
--   Local-oracle contracts, accuracy choices, and Frank–Wolfe execution
-- statement:
--   Each local set is convex and lies in its Euclidean unit ball. For every real objective $v$ and every $\tau>0$, the stipulated deterministic local service returns an actual point $x\in K_j$ satisfying
--   $$\langle v,x\rangle\ge\sup_{y\in K_j}\langle v,y\rangle-\tau.$$
--   No compactness is bundled into this contract. It implies nonemptiness of the original sets. For Euclidean balls the concrete oracle is $v/\|v\|$, with zero returned at $v=0$.
--
--   For optimization accuracy $\epsilon>0$, put $\epsilon_0=\min(\epsilon,1)$, $\eta=\epsilon_0/(8\sqrt m)$, $\delta=\epsilon_0/(4m)$, terminal tolerance $\epsilon_0/4$, and local net tolerance $\epsilon_0/(4k)$. Use $m=k$ when $k\le d^2$; otherwise use $m=\min(k,\lceil\sqrt{dk}\rceil)$ balanced consecutive blocks.
--
--   Weak membership first rejects $\|M\|_F\ge1+\epsilon$. Otherwise the squared-distance objective is $F(Y)=\|Y-M\|_F^2/2$. Starting at an actual locally obtained product point, the recorded update is $Y_{t+1}=(1-2/(t+2))Y_t+(2/(t+2))Z_t$. Each direction has a finite execution of a supplied code routine on $(M-Y_t)/\max(1,\|M-Y_t\|_F)$. Use $T=\lceil128/\epsilon_0^2\rceil+1$, normalized direction accuracy $\epsilon_0^2/[16(3+\epsilon)]$, and decision threshold $\epsilon^2/4$. The finite direction code is existentially constructed in the theorem, never assumed to be a global oracle. This definition contains no convergence or membership-correctness premise.
-- source:
--   Martino Bernasconi, Giulio Malavolta, STOC 2027 submission #945 (October 2026), pp.17–20, Lemma 5.1 and Theorem 5.2 proof; p.21, ball linear oracle

import Definitions.Def_NuclearTensor_Membership_Covers

set_option autoImplicit false
noncomputable section
open scoped BigOperators ENNReal

namespace NuclearTensor.Membership

def maxDimension (ds : List ℕ) : ℕ := ds.foldl max 0

def sourceSets (ds : List ℕ) (K : (j : ℕ) → Set (Vec (ds.getD j 0))) : Prop :=
  ∀ j < ds.length, Convex ℝ (K j) ∧ K j ⊆ unitBall (ds.getD j 0)

/-- The only assumed optimization is local, on the original feasible set, for every real
objective and every positive accuracy. This implies local nonemptiness without compactness. -/
def localOracleContract (O : LocalOracle)
    (K : (j : ℕ) → Set (Vec (O.dimensions.getD j 0))) : Prop :=
  ∀ (j : Fin O.dimensions.length) (v : Vec (O.dimensions.getD j.val 0)) (τ : ℝ),
    0 < τ → O.answer j v τ ∈ K j.val ∧
      ∀ y ∈ K j.val, inner ℝ v (O.answer j v τ) ≥ inner ℝ v y - τ

/-- The source's concrete ball oracle; zero objectives return the zero vector.
Its finite arithmetic implementation must be supplied when eliminating local calls in the goal. -/
def ballOracle (ds : List ℕ) : LocalOracle where
  dimensions := ds
  answer := fun _ v _ => ‖v‖⁻¹ • v

/-- The original unit-ball convention; finite nets contain actual feasible points. -/
def isNet {n : ℕ} (K : Set (Vec n)) (δ : ℝ) (N : List (Vec n)) : Prop :=
  (∀ y ∈ N, y ∈ K) ∧ ∀ x ∈ K, ∃ y ∈ N, ‖x - y‖ ≤ δ

def compressionAccuracy (ε : ℝ) (m : ℕ) : ℝ := min ε 1 / (8 * Real.sqrt m)
def coverAccuracy (ε : ℝ) (m : ℕ) : ℝ := min ε 1 / (4 * m)
def localNetAccuracy (ε : ℝ) (k : ℕ) : ℝ := min ε 1 / (4 * k)
def terminalAccuracy (ε : ℝ) : ℝ := min ε 1 / 4

/-- Exactly the source's small- and large-order split; balanced consecutive blocks. -/
def blockCount (ds : List ℕ) : ℕ :=
  if ds.length ≤ maxDimension ds ^ 2 then ds.length
  else min ds.length (Nat.ceil (Real.sqrt (maxDimension ds * ds.length)))

def block (ds : List ℕ) (m j : ℕ) : List ℕ :=
  (ds.drop (j * ds.length / m)).take (((j + 1) * ds.length / m) - j * ds.length / m)

def groupedDimensions (ds : List ℕ) (m : ℕ) : List ℕ :=
  (List.range m).map fun j => (block ds m j).prod

/-- Cover-subroutine input: shape, compression ranks; then η, δ, M, and compression arrays. -/
def coverInputIntegers {ds : List ℕ} (C : PrefixData ds) : List ℤ :=
  (ds.map Int.ofNat) ++ encodePrefixIntegers C

def coverInputReals {ds : List ℕ} (η δ : ℝ) (M : Tensor ds) (C : PrefixData ds) : List ℝ :=
  [η, δ] ++ encodeVec M ++ encodePrefixReals C

/-- Exact source terminal subroutine. It outputs an actual last-factor maximizer,
for every p. Its time is an execution bound, not an attached numerical certificate. -/
def terminalContract (σ : Spectral) (ω : Option LocalOracle) (A q : ℕ)
    {ds : List ℕ} (C : PrefixData ds)
    (K : (j : ℕ) → Set (Vec (ds.getD j 0))) (P : Program) (Tterm : ℝ) : Prop :=
  ∀ p : Vec (C.rank (ds.length - 1)),
    runsWithin σ ω A q [] P
      [C.rank (ds.length - 1), ds.getD (ds.length - 1) 0]
      (encodeVec (C.tensor (ds.length - 1)) ++ encodeVec p) Tterm
      (fun s => ∃ x ∈ K (ds.length - 1), ∃ value : ℝ,
        outputReals s = value :: encodeVec x ∧
        value = (∑ a : Fin (C.rank (ds.length - 1)), ∑ b : Fin (ds.getD (ds.length - 1) 0),
          entry (C.tensor (ds.length - 1))
            (a.val * ds.getD (ds.length - 1) 0 + b.val) * p a * x b) ∧
        ∀ y ∈ K (ds.length - 1),
          value ≥ (∑ a : Fin (C.rank (ds.length - 1)), ∑ b : Fin (ds.getD (ds.length - 1) 0),
            entry (C.tensor (ds.length - 1))
              (a.val * ds.getD (ds.length - 1) 0 + b.val) * p a * y b))

def coverContract (σ : Spectral) (ω : Option LocalOracle) (A q : ℕ)
    {ds : List ℕ} (η δ : ℝ) (M : Tensor ds) (C : PrefixData ds)
    (K : (j : ℕ) → Set (Vec (ds.getD j 0))) (P : Program) (Tcover : ℝ) : Prop :=
  runsWithin σ ω A q [] P (coverInputIntegers C) (coverInputReals η δ M C) Tcover
    (fun s => ∃ S : FiniteCover C, outputsCover s S ∧ finiteCoverProperty C K δ S)

/-- Direct vector/scalar cases use exact Euclidean membership. No bound on M is imposed. -/
def baseCaseDecision {d k : ℕ} (M : Tensor (List.replicate k d)) (b : Bool) : Prop :=
  d = 1 ∨ k = 1 → (b = true ↔ ‖M‖ ≤ 1)

/-- An actual starting product point, selected only using the stipulated local service. -/
def initialTuple (O : LocalOracle) : Tuple O.dimensions := fun j =>
  if h : j < O.dimensions.length then
    O.answer ⟨j, h⟩ (WithLp.toLp 2 (fun _ => 0)) 1
  else WithLp.toLp 2 (fun _ => 0)

def fwSteps (ε : ℝ) : ℕ := Nat.ceil (128 / (min ε 1) ^ 2) + 1
def fwOracleAccuracy (ε : ℝ) : ℝ := (min ε 1) ^ 2 / (16 * (3 + ε))

def normalizedDirection {n : ℕ} (M Y : Vec n) : Vec n :=
  (max 1 ‖M - Y‖)⁻¹ • (M - Y)

/-- The exact norm-rejection branch and the arithmetic Frank--Wolfe update. The direction
subroutine is supplied as finite code; each invocation below has a genuine execution.
There is no global optimizer primitive and no convergence/correctness field in this definition. -/
def frankWolfeBehavior (σ : Spectral) (A q : ℕ) (O : LocalOracle)
    (Pdir : Program) (ε : ℝ) (M : Tensor O.dimensions) (b : Bool) : Prop :=
  if 1 + ε ≤ ‖M‖ then b = false else
    ∃ (Y : ℕ → Tensor O.dimensions) (z : ℕ → Tuple O.dimensions),
      Y 0 = product (initialTuple O) ∧
      (∀ t < fwSteps ε,
        (∃ s c, Executes σ (some O) A q [Pdir] Pdir
          (initConfig (O.dimensions.map Int.ofNat)
            ([fwOracleAccuracy ε] ++ encodeVec (normalizedDirection M (Y t)))) s c ∧
          outputsTuple s (z t)) ∧
        Y (t + 1) = (1 - (2 : ℝ) / (t + 2)) • Y t +
          ((2 : ℝ) / (t + 2)) • product (z t)) ∧
      (b = true ↔ ‖Y (fwSteps ε) - M‖ ^ 2 / 2 ≤ ε ^ 2 / 4)

end NuclearTensor.Membership


