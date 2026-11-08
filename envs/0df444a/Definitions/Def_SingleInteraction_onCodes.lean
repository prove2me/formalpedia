-- Prove2me | Definitions.Def_SingleInteraction_onCodes
-- name    : SingleInteraction_onCodes
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:53:44.398315+00:00
-- url     : https://prove2.me/theorems/6050a7ba-7a3b-45f6-86c4-6c0bf1a550ea
-- title:
--   A promise problem on instances, transported to bit strings
-- statement:
--   A promise problem is a pair $(L_{\mathrm{yes}},L_{\mathrm{no}})$ of disjoint sets. Given a uniquely decodable binary code of the instances, the problem on bit strings has as yes-set (no-set) the codes of the yes-instances (no-instances); other strings are outside the promise.
--
--   The published QMA class is a predicate on promise problems over bit strings; this transport is how the instance problems of the mission are placed in QMA.
--
--   **Formalization Note** The two images are disjoint because a codec's encoding is injective (proved in the module).
-- source:
--   Hecker, The Complexity of Single-Interaction Hamiltonians, arXiv:2609.39592 (held version, sha256 19ddc444…), §2.2, p.15 (promise problems)

import Mathlib
import Definitions.Def_ContinuumCoulombHardness

open OAI.ContinuumCoulomb OAI.ContinuumCoulomb.BinaryEncoding

namespace SingleInteraction

/-- A codec's encoding is injective: `read` recovers the value from its code. -/
theorem codec_encode_injective {α : Type} (C : Codec α) : Function.Injective C.encode := by
  intro x y hxy
  have hx := C.read_encode x []
  have hy := C.read_encode y []
  rw [hxy, hy] at hx
  exact (Prod.mk.inj hx).1.symm

/-- A promise problem on instances, transported to bit strings through a codec (Hecker, *The Complexity of Single-Interaction Hamiltonians*, arXiv:2609.39592 (held version, sha256 19ddc444…), §2.2, p.15:
"A promise problem is a pair `L = (Lyes, Lno)` of disjoint sets of strings").

**Formalization Note** The yes- and no-sets are the images of those of `P` under `C.encode`; they are
disjoint because the encoding is injective (`codec_encode_injective`). Bit strings outside both images
are outside the promise. This is the form in which the published `InQMA`
(`OAI.ContinuumCoulomb.InQMA`, a predicate on bit-string promise problems) applies to an instance
problem. -/
def onCodes {α : Type} (C : Codec α) (P : PromiseProblem α) : PromiseProblem BitString where
  yes := C.encode '' P.yes
  no := C.encode '' P.no
  disjoint := by
    rw [Set.disjoint_left]
    rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, hxy⟩
    obtain rfl := codec_encode_injective C hxy
    exact Set.disjoint_left.mp P.disjoint hx hy

end SingleInteraction


