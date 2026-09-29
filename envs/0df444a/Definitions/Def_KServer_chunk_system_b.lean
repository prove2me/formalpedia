-- Prove2me | Definitions.Def_KServer_chunk_system_b
-- name    : KServer_chunk_system_b
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-01T10:06:41.681592+00:00
-- url     : https://prove2.me/theorems/370141ae-0823-44b4-ac5c-e9bb1c9706d9
-- title:
--   Chunk systems with online escapes: the BCR Lemma 6 package, final form
-- statement:
--   The **final form of the BCR Lemma 6 induction package**: a filtered chunk system whose conditional cost bounds are stated against every deterministic evader and every **online escape rule** (`bailCost` of `KServer_evader_bail`), with strictly positive outcome weights.
--
--   Relative to `KServer_chunk_system_f`: (i) escape costs are online (`bailCost`) rather than the pointwise minimum — offline-escape bounds imply these pointwise, and only the online form composes under chunk combining, where the charging argument needs the escape event to be adapted; (ii) weights are strictly positive, so every atom has positive mass and conditional expectations are well-defined without conventions.
--
--   All other conditions are as in Lemma 6: an explicit refining filtration with chunks adapted and sizes predictable, nonempty requests, last request $\{t\}$, offline evader cost at most $d(s,t)$ from $s$, sizes in $[c_{\mathrm{Lo}}, c_{\mathrm{Hi}}]$, expected total at least `total`, at least $m_{\mathrm{Lo}}$ chunks.
-- source:
--   S. Bubeck, C. Coester, Y. Rabani, 'The randomized k-server conjecture is false!', STOC 2023, Lemma 6 and Lemma 10.

import Mathlib
import Definitions.Def_KServer_evader
import Definitions.Def_KServer_evader_bail

namespace KServer

/-- A **chunk system with online escapes** on a metric space with marked points
`s, t`: the induction package of BCR's Lemma 6. A finitely supported random
sequence of `m` chunks of set requests with adapted sizes, an explicit refining
filtration (atoms encoded by `hist : ℕ → Ω → ℕ`), strictly positive outcome
weights, and the conditional cost bound stated against every evader and every
**online escape rule** (`bailCost`) with escape price `price` on the current
chunk. Sizes lie in `[cLo, cHi]`, the expected total size is at least `total`,
and there are at least `mLo` chunks. -/
structure ChunkSystemB (X : Type*) [MetricSpace X] (s t : X)
    (cLo cHi total price : ℝ) (mLo : ℕ) where
  /-- the finite sample space -/
  Ω : Type
  [instFin : Fintype Ω]
  [instDec : DecidableEq Ω]
  /-- outcome weights -/
  P : Ω → ℝ
  /-- the number of chunks -/
  m : ℕ
  /-- the filtration: time-`i` knowledge, encoded as atoms -/
  hist : ℕ → Ω → ℕ
  /-- the chunks -/
  chunk : Ω → Fin m → List (Set X)
  /-- the sizes -/
  size : Ω → Fin m → ℝ
  hP : ∀ ω, 0 < P ω
  hPsum : ∑ ω, P ω = 1
  hm : mLo ≤ m
  hm0 : 0 < m
  href : ∀ i j : ℕ, i ≤ j → ∀ ω ω', hist j ω = hist j ω' → hist i ω = hist i ω'
  hadapt : ∀ (i : Fin m) (ω ω' : Ω), hist (i + 1) ω = hist (i + 1) ω' →
    chunk ω i = chunk ω' i
  hsmeas : ∀ (i : Fin m) (ω ω' : Ω), hist i ω = hist i ω' → size ω i = size ω' i
  hne : ∀ ω i, ∀ S ∈ chunk ω i, S.Nonempty
  hlast : ∀ ω, (((List.ofFn (chunk ω)).flatten).getLast?) = some {t}
  hopt : ∀ ω, evaderOfflineCost s ((List.ofFn (chunk ω)).flatten) ≤ dist s t
  hsize : ∀ ω i, cLo ≤ size ω i ∧ size ω i ≤ cHi
  hcost : ∀ (i : Fin m) (ω₀ : Ω) (E : EvaderAlgorithm X) (bail : List (Set X) → Bool),
    size ω₀ i * (∑ ω ∈ Finset.univ.filter (fun ω => hist i ω = hist i ω₀), P ω)
      ≤ ∑ ω ∈ Finset.univ.filter (fun ω => hist i ω = hist i ω₀),
        P ω * E.bailCost bail (((List.ofFn (chunk ω)).take i).flatten) (chunk ω i) price
  htotal : total ≤ ∑ ω, P ω * (∑ i, size ω i)

attribute [instance] ChunkSystemB.instFin ChunkSystemB.instDec

/-- The flattened request sequence of an outcome. -/
def ChunkSystemB.seq {X : Type*} [MetricSpace X] {s t : X} {cLo cHi total price : ℝ}
    {mLo : ℕ} (C : ChunkSystemB X s t cLo cHi total price mLo) (ω : C.Ω) : List (Set X) :=
  (List.ofFn (C.chunk ω)).flatten

end KServer


