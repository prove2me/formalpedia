-- Prove2me | Definitions.Def_PoSUndirected_Supplement_OwnerRankClassSupremum
-- name    : PoSUndirected_Supplement_OwnerRankClassSupremum
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T00:31:07.933292+00:00
-- url     : https://prove2.me/theorems/7cd2eb2a-f1da-4625-992c-89e0423f57fe
-- title:
--   Endpoint-owner subclasses, exact PoS suprema and binary polynomial-time selection
-- statement:
--   An owned-subset game has one independently labelled endpoint owner for every edge of a nonempty subset $E_{\mathrm{own}}\subseteq E$; no player is attached to an unowned edge. An owned-forest game has $m_f$ independent endpoint owners of each $f\in F$ and exactly $s$ additional independently labelled players sharing one terminal pair, which the paper permits to be trivial.
--
--   Exact class suprema are expressed in both directions: every finite positive-OPT instance has a strict upper bound $q<K$, and for every $\varepsilon>0$ another finite instance has $q>K-\varepsilon$. Mathematical instances have arbitrary positive real costs. Separate algorithmic instances have positive rational costs and explicit binary encodings. Polynomial time means Mathlib's multi-tape Turing-machine notion; the compressed output records each direct owner edge and its multiplicity and then the additional group's common path and multiplicity. For the all-trivial zero-OPT corner, it records the paper's zero-cost equilibrium conclusion instead of forming an ordinary ratio.
-- source:
--   Tsoufis, The Price of Stability in Undirected Network Design: Lower Bounds and Structural Guarantees (preprint, sha256 c095d811fa04b471d74ba4fdab8fb89ccb3d34079d3bf07384f46ac57144866c), Theorems 4.3 and 4.5, pp.8,10 (PDF pp.10,12); Proposition B.10, p.54 (PDF p.56); Appendix C, pp.56–58 (PDF pp.58–60)

import Mathlib
import Definitions.Def_PoSUndirected_Supplement_MaxBlockRankLE

open CongestionPoA.AsymSum PriceOfStability.Harmonic

set_option autoImplicit false

namespace PoSUndirected.Supplement

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-! ## Endpoint-owner subclasses and the binary algorithmic interfaces of Theorems 4.3 and 4.5 -/

/-- The equal-sharing game with one endpoint owner for every edge in the (possibly proper) subset
`owned`.  The player labels retain the physical edge they own. -/
noncomputable def subsetOwnerGame (ends : E → Sym2 V) (c : E → ℝ) (owned : Finset E) :
    CongestionGame {e : E // e ∈ owned} E :=
  fairGame (fun e ↦ ownerStrategies ends e.1) (fun e _ ↦ c e)

/-- A standardized finite real-cost owner instance for the mathematical bound and class supremum. -/
structure OwnerRealInstance where
  nV : ℕ
  nE : ℕ
  ends : Fin nE → Sym2 (Fin nV)
  c : Fin nE → ℝ
  owned : Finset (Fin nE)

def OwnerRealInstance.Valid (I : OwnerRealInstance) (r : ℕ) : Prop :=
  I.owned.Nonempty ∧ IsLoopless I.ends ∧ (∀ e, 0 < I.c e) ∧ MaxBlockRankLE I.ends r

noncomputable def OwnerRealInstance.game (I : OwnerRealInstance) :
    CongestionGame {e : Fin I.nE // e ∈ I.owned} (Fin I.nE) :=
  subsetOwnerGame I.ends I.c I.owned

/-- A standardized finite owner instance.  Using `Fin n` loses no finite instance up to relabelling
and permits one uniform binary-input algorithm. -/
structure OwnerInstance where
  nV : ℕ
  nE : ℕ
  ends : Fin nE → Sym2 (Fin nV)
  c : Fin nE → ℚ
  owned : Finset (Fin nE)

/-- The structural class in Theorem 4.3. -/
def OwnerInstance.Valid (I : OwnerInstance) (r : ℕ) : Prop :=
  I.owned.Nonempty ∧ IsLoopless I.ends ∧ (∀ e, 0 < I.c e) ∧ MaxBlockRankLE I.ends r

/-- The owner game represented by a standardized instance. -/
noncomputable def OwnerInstance.game (I : OwnerInstance) :
    CongestionGame {e : Fin I.nE // e ∈ I.owned} (Fin I.nE) :=
  subsetOwnerGame I.ends (fun e ↦ (I.c e : ℝ)) I.owned

/-- The assertion that `K` is the exact (unattained, instancewise strict) supremum of ordinary PoS
over endpoint-owner games of maximum block rank at most `r`. -/
def OwnerRankClassSupremum (r : ℕ) (K : ℝ) : Prop :=
  (∀ (I : OwnerRealInstance) (q : ℝ), I.Valid r → OrdinaryPoSValue I.game I.c q → q < K) ∧
  ∀ ε : ℝ, 0 < ε → ∃ (I : OwnerRealInstance) (q : ℝ),
    I.Valid r ∧ OrdinaryPoSValue I.game I.c q ∧ K - ε < q

/-! Binary encodings.  Naturals are self-delimited little-endian binary strings; rationals use a
sign bit, numerator and positive denominator.  Graph endpoints are encoded by their full incidence
table, so parallel physical edges remain separately labelled. -/

def binaryNat (n : ℕ) : List Bool :=
  n.bits.flatMap (fun b ↦ [true, b]) ++ [false]

def binaryInt (z : ℤ) : List Bool :=
  decide (z < 0) :: binaryNat z.natAbs

def binaryRat (q : ℚ) : List Bool :=
  binaryInt q.num ++ binaryNat q.den

def encodeOwnerInstance (I : OwnerInstance) : List Bool :=
  binaryNat I.nV ++ binaryNat I.nE ++
    (List.ofFn fun e : Fin I.nE ↦
      (List.ofFn fun u : Fin I.nV ↦
        (List.ofFn fun v : Fin I.nV ↦ decide (I.ends e = s(u, v)))).flatten).flatten ++
    (List.ofFn fun e : Fin I.nE ↦ binaryRat (I.c e)).flatten ++
    List.ofFn (fun e : Fin I.nE ↦ decide (e ∈ I.owned))

def encodeFinset {n : ℕ} (S : Finset (Fin n)) : List Bool :=
  List.ofFn fun i : Fin n ↦ decide (i ∈ S)

def encodeOwnerProfile (I : OwnerInstance)
    (P : {e : Fin I.nE // e ∈ I.owned} → Finset (Fin I.nE)) : List Bool :=
  (List.ofFn fun e : Fin I.nE ↦
    if h : e ∈ I.owned then encodeFinset (P ⟨e, h⟩) else List.replicate I.nE false).flatten

/-- Polynomial-time exact cheapest-equilibrium selection for the rank-`r` owner class.  The
machine reads the explicit binary graph/cost/owned-set encoding and returns the incidence matrix of
a cheapest equilibrium profile. -/
def HasPolynomialCheapestOwnerAlgorithm (r : ℕ) : Prop :=
  ∃ f : List Bool → List Bool,
    Nonempty (Turing.TM2ComputableInPolyTime (id : List Bool → List Bool)
      (id : List Bool → List Bool) f) ∧
    ∀ I : OwnerInstance, I.Valid r → ∃ P : {e : Fin I.nE // e ∈ I.owned} → Finset (Fin I.nE),
      IsCheapestEquilibrium I.game (fun e ↦ (I.c e : ℝ)) P ∧
        f (encodeOwnerInstance I) = encodeOwnerProfile I P

/-! ### One additional demand group on an owned forest -/

/-- Players in Theorem 4.5: `m_f` independently labelled copies of every forest-edge owner, and
exactly `s` independently labelled members of the one remaining common-terminal group. -/
abbrev AdditionalPlayer (F : Finset E) (m : E → ℕ) (s : ℕ) :=
  (Sigma fun f : {e : E // e ∈ F} ↦ Fin (m f.1)) ⊕ Fin s

/-- The game of Theorem 4.5.  Owner copies retain all endpoint-to-endpoint paths; the additional
copies retain all paths between the common terminals `u,v`. -/
noncomputable def additionalGroupGame (ends : E → Sym2 V) (c : E → ℝ) (F : Finset E)
    (m : E → ℕ) (sN : ℕ) (u v : V) : CongestionGame (AdditionalPlayer F m sN) E :=
  fairGame
    (fun p ↦ match p with
      | Sum.inl owner => ownerStrategies ends owner.1.1
      | Sum.inr _ => pathStrategies ends u v)
    (fun e _ ↦ c e)

/-- The compressed equilibrium form used by the algorithm: all owner copies use their own edge and
the `s` additional copies use the one recorded path `Q`. -/
def additionalDirectProfile (F : Finset E) (m : E → ℕ) (sN : ℕ) (Q : Finset E) :
    AdditionalPlayer F m sN → Finset E
  | Sum.inl owner => {owner.1.1}
  | Sum.inr _ => Q

/-- Standardized binary instance for the algorithmic clause of Theorem 4.5. -/
structure AdditionalGroupInstance where
  nV : ℕ
  nE : ℕ
  ends : Fin nE → Sym2 (Fin nV)
  c : Fin nE → ℚ
  F : Finset (Fin nE)
  m : Fin nE → ℕ
  r : ℕ
  sN : ℕ
  u : Fin nV
  v : Fin nV

def AdditionalGroupInstance.Valid (I : AdditionalGroupInstance) : Prop :=
  1 ≤ I.r ∧ 1 ≤ I.sN ∧ IsLoopless I.ends ∧ IsConnectedHost I.ends ∧
    (∀ e, 0 < I.c e) ∧
      IsForestInMinimumSpanningTree I.ends (fun e ↦ (I.c e : ℝ)) I.F ∧
    ∀ f ∈ I.F, I.r ≤ I.m f

noncomputable def AdditionalGroupInstance.game (I : AdditionalGroupInstance) :
    CongestionGame (AdditionalPlayer I.F I.m I.sN) (Fin I.nE) :=
  additionalGroupGame I.ends (fun e ↦ (I.c e : ℝ)) I.F I.m I.sN I.u I.v

/-- Real-cost instances for the mathematical statement and exact class supremum of Theorem 4.5. -/
structure AdditionalGroupRealInstance where
  nV : ℕ
  nE : ℕ
  ends : Fin nE → Sym2 (Fin nV)
  c : Fin nE → ℝ
  F : Finset (Fin nE)
  m : Fin nE → ℕ
  r : ℕ
  sN : ℕ
  u : Fin nV
  v : Fin nV

def AdditionalGroupRealInstance.Valid (I : AdditionalGroupRealInstance) : Prop :=
  1 ≤ I.r ∧ 1 ≤ I.sN ∧ IsLoopless I.ends ∧ IsConnectedHost I.ends ∧
    (∀ e, 0 < I.c e) ∧ IsForestInMinimumSpanningTree I.ends I.c I.F ∧
    ∀ f ∈ I.F, I.r ≤ I.m f

noncomputable def AdditionalGroupRealInstance.game (I : AdditionalGroupRealInstance) :
    CongestionGame (AdditionalPlayer I.F I.m I.sN) (Fin I.nE) :=
  additionalGroupGame I.ends I.c I.F I.m I.sN I.u I.v

def encodeAdditionalGroupInstance (I : AdditionalGroupInstance) : List Bool :=
  binaryNat I.nV ++ binaryNat I.nE ++ binaryNat I.r ++ binaryNat I.sN ++
    binaryNat I.u.val ++ binaryNat I.v.val ++
    (List.ofFn fun e : Fin I.nE ↦
      (List.ofFn fun u : Fin I.nV ↦
        (List.ofFn fun v : Fin I.nV ↦ decide (I.ends e = s(u, v)))).flatten).flatten ++
    (List.ofFn fun e : Fin I.nE ↦ binaryRat (I.c e)).flatten ++ encodeFinset I.F ++
    (List.ofFn fun e : Fin I.nE ↦ binaryNat (I.m e)).flatten

/-- Exact supremum of Theorem 4.5 for fixed positive `r,s`. -/
def AdditionalGroupClassSupremum (r sN : ℕ) (K : ℝ) : Prop :=
  (∀ (I : AdditionalGroupRealInstance) (q : ℝ), I.Valid → I.r = r → I.sN = sN →
    OrdinaryPoSValue I.game I.c q → q < K) ∧
  ∀ ε : ℝ, 0 < ε → ∃ (I : AdditionalGroupRealInstance) (q : ℝ),
    I.Valid ∧ I.r = r ∧ I.sN = sN ∧ OrdinaryPoSValue I.game I.c q ∧ K - ε < q

/-- The paper's compressed equilibrium output: one direct edge and its multiplicity for every
owner group, followed by the common additional-player path and its multiplicity. -/
def encodeCompressedAdditionalProfile (I : AdditionalGroupInstance) (Q : Finset (Fin I.nE)) :
    List Bool :=
  (List.ofFn fun e : Fin I.nE ↦
    if e ∈ I.F then true :: binaryNat (I.m e) else [false]).flatten ++
    encodeFinset Q ++ binaryNat I.sN

/-- One polynomial-time machine handles binary costs and binary multiplicities and outputs each
direct owner group and the common additional-player path once, together with their multiplicities. -/
def HasPolynomialCompressedAdditionalGroupAlgorithm : Prop :=
  ∃ f : List Bool → List Bool,
    Nonempty (Turing.TM2ComputableInPolyTime (id : List Bool → List Bool)
      (id : List Bool → List Bool) f) ∧
    ∀ I : AdditionalGroupInstance, I.Valid → ∃ Q : Finset (Fin I.nE),
      IsSimplePathEdges I.ends I.u I.v Q ∧
      IsPureNash I.game (additionalDirectProfile I.F I.m I.sN Q) ∧
      (∃ O, IsSocialOptimum I.game (fun e ↦ (I.c e : ℝ)) O ∧
        ((0 < socialCost (fun e ↦ (I.c e : ℝ)) O ∧
            socialCost (fun e ↦ (I.c e : ℝ)) (additionalDirectProfile I.F I.m I.sN Q) <
              (1 + 1 / ((I.r : ℝ) + I.sN)) * socialCost (fun e ↦ (I.c e : ℝ)) O) ∨
          (socialCost (fun e ↦ (I.c e : ℝ)) O = 0 ∧
            socialCost (fun e ↦ (I.c e : ℝ))
              (additionalDirectProfile I.F I.m I.sN Q) = 0))) ∧
        f (encodeAdditionalGroupInstance I) = encodeCompressedAdditionalProfile I Q

end PoSUndirected.Supplement


