-- Prove2me | Definitions.Def_SeedRecyclingDL_Codes_Interfaces
-- name    : SeedRecyclingDL_Codes_Interfaces
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:09:30.176449+00:00
-- url     : https://prove2.me/theorems/a04eac5d-093f-407f-a994-ac7bc3af2f5a
-- title:
--   Generic decoder assumptions, operational tag services, and bootstrap families
-- statement:
--   Generic listing assumptions require exact preimage and competitor sets, total membership/inversion, and actual terminating programs. A tag service has mathematical encoding and inverse functions together with a finite program whose executions establish the claimed query cost. These are hypotheses only where the source assumes an operational tag code.
--
--   The general-channel interface records every hypothesis of Theorem 3.3 and uses an effective greedy search for the first sufficient suffix length; the correction to its real-constant ceiling choice is documented in the audit notes. The bootstrap interface records an actual correct family, uniform programs for its message length and setup, and halting encoders and decoders with the source's monotone time bounds. None of these interfaces is an assumption of Theorem 1.1.
-- source:
--   Quan D. Bui, Manabu Hagiwara, Shuche Wang, Van Khu Vu, STOC 2027 submission #1449 (October 2026), §3, PDF pp. 10–12 (printed pp. 8–10); Appendix B, PDF pp. 18–19 (printed pp. 16–17); Appendix D.1, PDF pp. 24–25 (printed pp. 22–23); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1449.pdf

import Definitions.Def_SeedRecyclingDL_Codes_FieldExecution

set_option autoImplicit false

noncomputable section

namespace SeedRecyclingDL.Codes

/-- Algorithmic assumptions used only by the generic decoder, not the goal. -/
def ListingAlgorithms (n m : ℕ) (E : Channel) (Γ : Competitors)
    (A : Word → Word) (h N : ℕ) (preimages : Word → List Word)
    (inverse : Word → Option Word) : Prop :=
  (∀ y z : Word, z ∈ preimages y ↔ z.length = n ∧ y ∈ E n z) ∧
  (∀ u T : Word, inverse u = some T ↔ T.length = h ∧ u = A T) ∧
  ∃ pre comp inv : Program,
    (∀ y : Word, Halts pre n (y.map Fin.val) (some (packedWords (preimages y)))) ∧
    (∀ x : Word, x.length = m → Halts comp n (x.map Fin.val) (some (packedWords (Γ x).toList))) ∧
    (∀ u : Word, Halts inv n (u.map Fin.val) ((inverse u).map packedWord))

structure TagService where
  suffix : ℕ → ℕ
  encode : ℕ → Word → Word
  inverse : ℕ → Word → Option Word
  cells : ℕ → List ℕ
  query : Program
  time : ℕ → ℝ

def serviceCells (data : ℕ → FieldData) (S : TagService) (n : ℕ) : List ℕ :=
  [S.suffix n] ++ fieldDescriptor (data n).presentation ++ S.cells n

def OperationalTag (data : ℕ → FieldData) (S : TagService) (t n : ℕ) : Prop :=
  let N := S.suffix n
  TagCode (tagWidth t n) N (fun u v => Reaches (2 * t) u v) (S.encode n) ∧
  (∀ u T : Word, S.inverse n u = some T ↔ T.length = tagWidth t n ∧ u = S.encode n T) ∧
  ∀ saved : MachineState, SetupState (serviceCells data S n) saved →
    (∀ T : Word, T.length = tagWidth t n →
      ResumedExecutes S.query n saved ([0] ++ packedWord T)
        (some (packedWord (S.encode n T))) (S.time n)) ∧
    (∀ u : Word, u.length = N →
      ResumedExecutes S.query n saved ([1] ++ packedWord u)
        ((S.inverse n u).map packedWord) (S.time n))

def serviceEncoder (data : ℕ → FieldData) (S : TagService) (t n : ℕ) (mu : Word) : Word :=
  let P := (data n).presentation
  let m := n - S.suffix n
  encode P m (hashWidth t n) (competitorSet t m) (S.encode n)
    (mu.take m) ((mu.drop m).take (P.k - 1)) ((mu.drop (m + P.k - 1)).take (P.k - 1))

def serviceDecoder (data : ℕ → FieldData) (S : TagService) (t n : ℕ) (y : Word) : Option Word :=
  let m := n - S.suffix n
  procedureB2 (data n).presentation m (S.suffix n) (hashWidth t n)
    (competitorSet t m) (listPreimages t n) (S.inverse n) y

def servicePayload (data : ℕ → FieldData) (S : TagService) (t n : ℕ) (y : Word) : Option Word :=
  decodePayload (data n).presentation (n - S.suffix n) (S.suffix n) (hashWidth t n)
    (listPreimages t n) (S.inverse n) y

structure FamilyPrograms where
  messageLength : Program
  setup : Program
  encoder : Program
  decoder : Program

def FamilyAlgorithms (P : FamilyPrograms) (ell : ℕ) (M : ℕ → ℕ)
    (Enc : ℕ → Word → Word) (Dec : ℕ → Word → Option Word)
    (cells : ℕ → List ℕ) (theta setupTime onlineTime : ℕ → ℝ) : Prop :=
  Executes P.messageLength ell [] (some [M ell]) (theta ell) ∧
  ∃ saved : MachineState,
    SetupExecutes P.setup ell (cells ell) saved (setupTime ell) ∧
    (∀ mu : Word, mu.length = M ell →
      ResumedExecutes P.encoder ell saved (mu.map Fin.val)
        (some ((Enc ell mu).map Fin.val)) (onlineTime ell)) ∧
    (∀ y : Word, y.length = ell → ResumedExecutes P.decoder ell saved (y.map Fin.val)
      ((Dec ell y).map (List.map Fin.val)) (onlineTime ell)) ∧
    (∀ y : Word, ∃ bound : ℝ, ResumedExecutes P.decoder ell saved (y.map Fin.val)
      ((Dec ell y).map (List.map Fin.val)) bound)

def CorrectFamily (E : Channel) (M : ℕ → ℕ) (C : ℕ → Set Word)
    (Enc : ℕ → Word → Word) (Dec : ℕ → Word → Option Word) (ell : ℕ) : Prop :=
  Corrects E ell (C ell) ∧
  (∀ mu : Word, mu.length = M ell → Enc ell mu ∈ C ell) ∧
  (∀ mu nu : Word, mu.length = M ell → nu.length = M ell → Enc ell mu = Enc ell nu → mu = nu) ∧
  ∀ mu y : Word, mu.length = M ell → y ∈ E ell (Enc ell mu) → Dec ell y = some mu

/-- The input data of Theorem 3.3, kept separate from all its conclusions. -/
structure GeneralChannelData where
  channel : Channel
  competitors : ℕ → ℕ → ℕ → Competitors
  relation : ℕ → Word → Word → Prop
  L : ℕ → ℕ
  degreeConstant : ℝ
  degreeExponent : ℝ
  neighbors : ℕ → Word → List Word
  competitorList : ℕ → ℕ → ℕ → Word → List Word
  preimages : ℕ → Word → List Word

def GeneralChannelAssumptions (G : GeneralChannelData) : Prop :=
  ContainsInput G.channel ∧ 1 ≤ G.degreeConstant ∧ 0 ≤ G.degreeExponent ∧
  ∃ (n₀ d : ℕ) (K : ℝ) (len neigh comp pre : Program), 0 < K ∧
    ∀ n : ℕ, n₀ ≤ n → 1 ≤ G.L n ∧ log₂ (G.L n) ≤ K * log₂ n ∧
      Executes len n [] (some [G.L n]) (K * (n + 1 : ℝ) ^ d) ∧
      (∀ y z : Word, z ∈ G.preimages n y ↔ z.length = n ∧ y ∈ G.channel n z) ∧
      (∀ y : Word, Executes pre n (y.map Fin.val) (some (packedWords (G.preimages n y)))
        (K * (n + y.length + 1 : ℕ) ^ d)) ∧
      ∀ N : ℕ, 1 ≤ N → N ≤ n / 2 →
        let m := n - N
        Splittable G.channel m N (G.relation N) ∧
        ValidCompetitors m (G.L n) (G.competitors n m N) ∧
        (∀ x : Word, x.length = m →
          payloadCompetitors G.channel m N x ⊆ ↑(G.competitors n m N x)) ∧
        (∀ x : Word, x.length = m → (G.competitorList n m N x).toFinset = G.competitors n m N x ∧
          Executes comp n ([m, N] ++ x.map Fin.val) (some (packedWords (G.competitorList n m N x)))
            (K * (n + 1 : ℝ) ^ d)) ∧
        (∀ s : Word, s.length = N →
          (∀ u : Word, u ∈ G.neighbors N s ↔ u.length = N ∧ G.relation N s u) ∧
          (((G.neighbors N s).toFinset.card : ℕ) : ℝ) ≤ G.degreeConstant * (N : ℝ) ^ G.degreeExponent ∧
          Executes neigh N (s.map Fin.val) (some (packedWords (G.neighbors N s)))
            (K * (N + 1 : ℝ) ^ d))

def generalFieldWidth (G : GeneralChannelData) (n : ℕ) : ℕ :=
  EditMulticoloring.Code.ceilLog 2 (2 * G.L n * n)

def generalHashWidth (G : GeneralChannelData) (n : ℕ) : ℕ :=
  EditMulticoloring.Code.ceilLog 2 (2 * G.L n)

def generalTagWidth (G : GeneralChannelData) (n : ℕ) : ℕ :=
  2 * generalFieldWidth G n + generalHashWidth G n

/-- Effective form of the §3.3 choice: use the least suffix length for which
the actual greedy table contains enough words. This avoids executing a ceiling
of an arbitrary real exponent. The original ceiling still bounds the search. -/
def generalSuffix (G : GeneralChannelData) (n : ℕ) : ℕ :=
  let h := generalTagWidth G n
  (((List.range (n / 2 + 1 - h)).map fun i => h + i).find? fun N =>
    2 ^ h ≤ (greedyTable N (G.neighbors N)).length).getD 0

def generalDecoder (data : ℕ → FieldData) (G : GeneralChannelData) (n : ℕ) (y : Word) : Option Word :=
  let N := generalSuffix G n
  let m := n - N
  procedureB2 (data n).presentation m N (generalHashWidth G n) (G.competitors n m N)
    (G.preimages n) (tableInverse (generalTagWidth G n) (greedyTable N (G.neighbors N))) y

end SeedRecyclingDL.Codes


