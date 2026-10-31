-- Prove2me | Definitions.Def_SetCoverThreshold_SetCover_Theorem44
-- name    : SetCoverThreshold_SetCover_Theorem44
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-10-30T19:42:22.549706+00:00
-- url     : https://prove2.me/theorems/115c6496-7c3b-4ee9-905e-60166652c29b
-- title:
--   Set Cover Reduction Instance (Feige 1998, Theorem 4.4)
-- statement:
--   Given a 3CNF-5 formula $\varphi$, a $k$-prover code $\mathrm{code} : [k] \times [\ell] \to \{0, 1\}$, and a family of partition systems $P$ indexed by random strings $R \in [3M]^\ell$, the Section 4 Set Cover instance $\mathrm{scInst}(\varphi, \mathrm{code}, P)$ has ground set $U = (3M)^\ell \times [m]$ of size $N = |\varphi.\mathrm{Point}(\ell, m)|$, and a collection of subsets $S_x$ indexed by provers, questions, and answers $x \in \varphi.\mathrm{SetIdx}(\mathrm{code})$, where each set $S_x = \varphi.\mathrm{scSet}(\mathrm{code}, P, x)$ contains points $(R, b)$ consistent with the partition systems and prover answers (Feige 1998, Section 4, p. 645).
-- source:
--   Feige 1998, A Threshold of ln n for Approximating Set Cover, J. ACM 45(4): 634–652, Section 4, Lemma 4.1 and Theorem 4.4

import Definitions.Def_CookPvsNP_defs
import Definitions.Def_SetCoverThreshold_SetCover_Formula
import Definitions.Def_SetCoverThreshold_SetCover_ProofSystem
import Definitions.Def_SetCoverThreshold_SetCover_PartitionSystem
import Definitions.Def_SetCoverThreshold_SetCover_Instance
import Definitions.Def_SetCoverThreshold_SetCover_Reduction

set_option autoImplicit false

namespace SetCoverThreshold.SetCover

open Classical

/-- **The §4 Set Cover reduction instance** (Feige 1998, p. 645, proof of Lemma 4.1 and Theorem 4.4):
for a 3CNF-5 formula `φ`, a `k`-prover code `code : Fin k → Fin ℓ → Bool`, and a family of
partition systems `P : φ.RandomString ℓ → PartitionSystem m (2 ^ ℓ) k d`, the ground set has
`N = (3M)^ℓ · m` points (`φ.Point ℓ m`, indexed via `Fintype.equivFin`) and the subsets list
`φ.scSet code P x` for all `x : φ.SetIdx code`. -/
noncomputable abbrev scInst (φ : Formula5) {ℓ k m d : ℕ} (code : Fin k → Fin ℓ → Bool)
    (P : φ.RandomString ℓ → PartitionSystem m (2 ^ ℓ) k d) : SCInstance where
  n := Fintype.card (φ.Point ℓ m)
  sets := List.ofFn (fun i : Fin (Fintype.card (φ.SetIdx code)) =>
    (φ.scSet code P ((Fintype.equivFin (φ.SetIdx code)).symm i)).map
      (Fintype.equivFin (φ.Point ℓ m)).toEmbedding)

end SetCoverThreshold.SetCover


