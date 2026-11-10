-- Prove2me | Definitions.Def_CoarseMatching_LowerBound_ProtocolResources
-- name    : CoarseMatching_LowerBound_ProtocolResources
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T16:34:31.253455+00:00
-- url     : https://prove2.me/theorems/6427c185-8e5a-4e7c-ad74-7f7f95fb0722
-- title:
--   Communication costs, rounds, output and general input laws
-- statement:
--   The operational two-party model uses the referenced binary-tree and arbitrary probability-space tape primitives. The public tape may select the tree, including senders and stopping. Each selected tree is finite with local strategies, arbitrary independent public and private probability-space tapes, and Bob’s local output. There is no common depth bound across protocols. Swapping the two named input domains handles Alice’s local output. Each transmitted bit has the sender fixed by the tree, and consecutive bits from the same sender form an alternating message. Communication cost is the worst-case actual number of transmitted bits on the input promise.
--
--   $$\operatorname{gap}(\pi;\mu_0,\mu_1)=\left|\Pr_{\mu_1,\pi}[\mathrm{out}=1]-\Pr_{\mu_0,\pi}[\mathrm{out}=1]\right|.$$
--
--   Separate predicates bound total cost, exact message count and entrywise lengths, variable message-count bounds, first sender, and actual transmission of the final output bit. Preservation retains each such resource bound. Acceptance and success are computed from tree execution. General single-instance and XOR success use arbitrary probability measures on arbitrary measurable input domains, rather than finitely supported laws. Joint output measurability is the ordinary standing probability convention.
--
--   This resource layer extends the published fixed-tree protocol interface by public-coin-dependent tree choice, reusing its tree and tape definitions. It assumes no hardness or correctness conclusion.
-- source:
--   Gillat Kol, Even Coarse Matching Estimates Require Nearly Linear Streaming Space, STOC 2027 submission #1135 (October 2026), §3 and §§4.2–4.4, printed pp.10,12–16 (PDF pp.11,13–17). https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1135.pdf

import Definitions.Def_CaiZhuInfo_Matrix_Protocol

open MeasureTheory

namespace CoarseMatching.LowerBound
noncomputable section

abbrev BitTree := CaiZhuInfo.Matrix.CommunicationTree
instance bitTreeMeasurableSpace : MeasurableSpace BitTree := ⊤

/-- The published local tree/tape model extended to public-coin-dependent trees.
Thus public randomness may choose senders, stopping and message boundaries without
any conversion that could change the source's exact resource bounds. -/
structure Protocol (X Y : Type) where
  shared : CaiZhuInfo.Matrix.RandomSource
  privateA : CaiZhuInfo.Matrix.RandomSource
  privateB : CaiZhuInfo.Matrix.RandomSource
  tree : shared.Carrier → BitTree
  sendA : X → shared.Carrier → privateA.Carrier → List Bool → Bool
  sendB : Y → shared.Carrier → privateB.Carrier → List Bool → Bool
  out : Y → shared.Carrier → privateB.Carrier → List Bool → Bool
  tree_measurable : Measurable tree
  sendA_measurable : ∀ x h, Measurable (fun u : shared.Carrier × privateA.Carrier => sendA x u.1 u.2 h)
  sendB_measurable : ∀ y h, Measurable (fun u : shared.Carrier × privateB.Carrier => sendB y u.1 u.2 h)
  out_measurable : ∀ y h, Measurable (fun u : shared.Carrier × privateB.Carrier => out y u.1 u.2 h)

namespace Protocol
variable {X Y : Type} (P : Protocol X Y)
abbrev Coins := P.shared.Carrier × (P.privateA.Carrier × P.privateB.Carrier)
abbrev Sample := (X × Y) × P.Coins
abbrev Transcript := P.shared.Carrier × List Bool

def coinsLaw : Measure P.Coins := P.shared.law.prod (P.privateA.law.prod P.privateB.law)
instance coinsProbability : IsProbabilityMeasure P.coinsLaw := by
  dsimp [coinsLaw]
  infer_instance

def history (x : X) (y : Y) (c : P.Coins) : List Bool :=
  (P.tree c.1).execute (P.sendA x c.1 c.2.1) (P.sendB y c.1 c.2.2) []
def transcript (x : X) (y : Y) (c : P.Coins) : P.Transcript := (c.1, P.history x y c)
def output (x : X) (y : Y) (c : P.Coins) : Bool :=
  P.out y c.1 c.2.2 (P.history x y c)

def TranscriptDetermined : Prop :=
  ∃ g : P.Transcript → Bool, Measurable g ∧
    ∀ x y, (fun c => P.output x y c) =ᵐ[P.coinsLaw] (fun c => g (P.transcript x y c))
end Protocol

/-- Speaker of every actual transmitted bit, in order (false = Alice).
There is no information in silence, stopping, or message length: the tree determines these. -/
def BitTree.speakers : BitTree → (List Bool → Bool) → (List Bool → Bool) →
    List Bool → List Bool
  | .leaf, _, _, _ => []
  | .alice l r, a, b, h => false ::
      (if a h then BitTree.speakers r a b (h ++ [true])
       else BitTree.speakers l a b (h ++ [false]))
  | .bob l r, a, b, h => true ::
      (if b h then BitTree.speakers r a b (h ++ [true])
       else BitTree.speakers l a b (h ++ [false]))

/-- Maximal consecutive transmissions by one party constitute a message. -/
def segments : List Bool → List (Bool × ℕ)
  | [] => []
  | b :: bs => match segments bs with
    | [] => [(b,1)]
    | (c,k) :: cs => if b = c then (c,k+1) :: cs else (b,1) :: (c,k) :: cs

def messages {X Y : Type} (P : Protocol X Y) (x : X) (y : Y) (c : P.Coins) :=
  segments (BitTree.speakers (P.tree c.1) (P.sendA x c.1 c.2.1) (P.sendB y c.1 c.2.2) [])

/-- Worst-case transmitted bits; local output is not charged unless actually sent.
The section-4 conclusions separately require transcript-determined output. -/
def CostOn {X Y : Type} (D : X → Y → Prop) (P : Protocol X Y) (L : ℝ) : Prop :=
  ∀ x y, D x y → ∀ c : P.Coins, ((P.history x y c).length : ℝ) ≤ L

/-- Exactly one alternating message per entry of bs, with
entrywise bit bounds. Zero bits cannot act as an uncharged signal. -/
def ProfileOn {X Y : Type} (D : X → Y → Prop) (P : Protocol X Y) (bs : List ℕ) : Prop :=
  ∀ x y, D x y → ∀ c : P.Coins,
    let ms := messages P x y c
    ms.length = bs.length ∧
      ∀ i : ℕ, (ms[i]?.map Prod.snd).getD 0 ≤ bs[i]?.getD 0

/-- The first sender is separately specified; both orientations are allowed. -/
def StartsWithOn {X Y : Type} (D : X → Y → Prop) (P : Protocol X Y) (b : Bool) : Prop :=
  ∀ x y, D x y → ∀ c : P.Coins, (messages P x y c).head?.map Prod.fst = some b

/-- Round and entrywise bounds also cover protocols whose number of rounds varies. -/
def BoundsOn {X Y : Type} (D : X → Y → Prop) (P : Protocol X Y) (bs : List ℕ) : Prop :=
  ∀ x y, D x y → ∀ c : P.Coins,
    (messages P x y c).length ≤ bs.length ∧
      ∀ i : ℕ, ((messages P x y c)[i]?.map Prod.snd).getD 0 ≤ bs[i]?.getD 0

/-- Section 4 sends its final output bit and counts it. -/
def OutputSentOn {X Y : Type} (D : X → Y → Prop) (P : Protocol X Y) : Prop :=
  ∀ x y, D x y → ∀ c : P.Coins,
    (P.history x y c).getLast? = some (P.output x y c)

/-- Exact preservation of all advertised per-message and total resource bounds. -/
def Preserves {X Y X' Y' : Type} (D : X → Y → Prop) (E : X' → Y' → Prop)
    (P : Protocol X Y) (Q : Protocol X' Y') : Prop :=
  (∀ L, CostOn D P L → CostOn E Q L) ∧
  (∀ bs, ProfileOn D P bs → ProfileOn E Q bs) ∧
  (∀ bs, BoundsOn D P bs → BoundsOn E Q bs) ∧
  (∀ b, StartsWithOn D P b → StartsWithOn E Q b)

/-- General (not necessarily atomic) input laws. No finite-domain restriction. -/
def success {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y]
    (P : Protocol X Y) (μ : ProbabilityMeasure (X × Y)) (f : X → Y → Bool) : ℝ :=
  (((μ : Measure (X × Y)).prod P.coinsLaw)
    {s | P.output s.1.1 s.1.2 s.2 = f s.1.1 s.1.2}).toReal

/-- The ordinary standing measurability convention, including joint execution.
This asserts no correctness, cost, or hardness property. -/
def MeasurableProtocol {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y]
    (P : Protocol X Y) : Prop :=
  Measurable (fun s : P.Sample => P.output s.1.1 s.1.2 s.2)

/-- Success on independent instances of an arbitrary probability law. -/
def xorSuccess {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y] (t : ℕ)
    (P : Protocol (Fin t → X) (Fin t → Y)) (μ : ProbabilityMeasure (X × Y))
    (f : X → Y → Bool) : ℝ :=
  ((Measure.pi (fun _ : Fin t => (μ : Measure (X × Y)))).prod P.coinsLaw
    {s | P.output (fun i => (s.1 i).1) (fun i => (s.1 i).2) s.2 =
      (List.ofFn (fun i : Fin t => f (s.1 i).1 (s.1 i).2)).foldl xor false}).toReal

/-- Average acceptance under a finite law, computed from local tree execution. -/
def acceptance {X Y : Type} [Fintype X] [Fintype Y]
    (P : Protocol X Y) (μ : PMF (X × Y)) : ℝ :=
  ∑ xy, (μ xy).toReal * (P.coinsLaw {c | P.output xy.1 xy.2 c = true}).toReal

def gap {X Y : Type} [Fintype X] [Fintype Y] (P : Protocol X Y)
    (μ₀ μ₁ : PMF (X × Y)) : ℝ := |acceptance P μ₁ - acceptance P μ₀|

end
end CoarseMatching.LowerBound


