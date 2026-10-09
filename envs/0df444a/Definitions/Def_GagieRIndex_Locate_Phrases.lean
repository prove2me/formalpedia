-- Prove2me | Definitions.Def_GagieRIndex_Locate_Phrases
-- name    : GagieRIndex_Locate_Phrases
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T20:21:31.662594+00:00
-- url     : https://prove2.me/theorems/3eb89fe1-8375-457e-9e4a-ff2461a2d19c
-- title:
--   Definition 3, p. 12 and §5.3, pp. 22–23 — the phrase head of T[k] and the phrases of ISA
-- statement:
--   Definition 3 parses the text $T$ into **phrases** so that $T[i]$ is the first character of a phrase if and only if $T[i]$ is sampled. For a text position $k$, the **phrase head** of $T[k]$ is the position $i$ of the first character of the phrase containing $T[k]$, that is, the greatest sampled position not exceeding $k$:
--   $$\operatorname{head}(k)=\max\{\,i\le k : T[i]\text{ is sampled}\,\},\qquad \operatorname{head}(k)=0\ \text{ if no sampled position is}\le k.$$
--
--   Section 5.3 uses a second parse. A text position $i$ **starts a phrase of $ISA$** if $i=SA[p]$ for a position $p$ at which a new run starts in the BWT, i.e. $ISA[i]$ is a run start; last positions of runs do not start phrases of $ISA$.
--
--   The phrase head is what a predecessor search over the sampled positions returns in the proof of Lemma 3; the $ISA$ phrases govern when $\phi$ shifts consecutive positions consecutively (Lemma 14). The two parses are different and are kept apart.
--
--   **Formalization Note** The value $0$ encodes the phrase that wraps around through $T[n]=\$$: $T[1]$ need not be sampled, but $T[n]$ always is, so for small $k$ the phrase containing $T[k]$ began at $T[n]$. Reading $T[0]$ as $T[n]$, exactly as in the definition of the BWT, its head is position $0$. The phrase head is defined from the sampled set by a maximum, never through the LF mapping.
-- source:
--   Gagie, Navarro, Prezza, Fully-Functional Suffix Trees and Optimal Text Searching in BWT-runs Bounded Space, arXiv:1809.02792v2, p. 12, Definition 3 and proof of Lemma 3; pp. 22–23, §5.3

import Mathlib
import Definitions.Def_GagieRIndex_Locate_Core

namespace GagieRIndex.Locate

/-- The phrase head of `T[k]`: the text position `i` of the first character of the phrase containing
`T[k]` (Definition 3, p. 12; proof of Lemma 3, p. 12), i.e. the greatest sampled position `i ≤ k`.
If no sampled position is `≤ k`, the phrase containing `T[k]` wraps through `T[n] = $` and the value
is `0`, read as `T[0] ≡ T[n]` as in the definition of `BWT` (p. 8). -/
def phraseHead (n : ℕ) (T SA : ℕ → ℕ) (k : ℕ) : ℕ :=
  ((sampled n T SA).filter (· ≤ k)).sup id

/-- Text position `i` starts a phrase of `ISA` (§5.3, pp. 22–23): `i = SA[p]` for a position `p`
where a new run starts in `BWT`, i.e. `ISA[i]` is a run start (last positions of runs do not start
phrases). -/
def IsISAPhraseStart (n : ℕ) (T SA : ℕ → ℕ) (i : ℕ) : Prop :=
  IsRunStart n T SA (ISA n SA i)

instance (n : ℕ) (T SA : ℕ → ℕ) : DecidablePred (IsISAPhraseStart n T SA) := fun _ => by
  unfold IsISAPhraseStart; infer_instance

end GagieRIndex.Locate


