-- Prove2me | Definitions.Def_HierADA_blocksMass
-- name    : HierADA_blocksMass
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:57:50.788454+00:00
-- url     : https://prove2.me/theorems/bf8c6e0b-7709-465e-9c75-eb545d1be81f
-- title:
--   Law of the independent sample blocks
-- statement:
--   For a distribution $P$ on a domain $X$ and block sizes $n_1,\dots,n_p$, the sample blocks $S_j=(X_{j,1},\dots,X_{j,n_j})$ are independent i.i.d. samples from $P$. The probability of a value $S$ is
--
--   $$
--   \prod_{j=1}^pP^{n_j}(S_j).
--   $$
--
--   **Formalization Note** $P^{n}$ is the published `IsRandomnessNecessaryADA.Plain.iid`.
-- source:
--   Gribelyuk–Lin–Lyu–Majid–Woodruff–Yu–Zhou, Adaptive Data Analysis and Adversarial Robustness on Insertion-Deletion Streams, preprint (version of 2026-11-03, sha256 f220ae51…), Section 3, p.13

import Mathlib
import Definitions.Def_IsRandomnessNecessaryADA_Plain_Protocol

set_option autoImplicit false

namespace HierADA

/-- **The law of the independent sample blocks** — Gribelyuk–Lin–Lyu–Majid–Woodruff–Yu–Zhou, *Adaptive
Data Analysis and Adversarial Robustness on Insertion-Deletion Streams*, preprint (version of
2026-11-03, sha256 f220ae51…), Section 3, p.13: "Given `p` independent blocks of samples from an
unknown distribution `D`, … `S_j = (X_{j,1}, …, X_{j,n_j})`".

The probability mass of the blocks `S` when every block `S_j` is an i.i.d. sample of size `n_j` from
`P` (the published `iid`) and the blocks are independent: `∏_j P^{n_j}(S_j)`. -/
noncomputable def blocksMass {X : Type} (P : PMF X) {p : ℕ} (n : Fin p → ℕ)
    (S : (j : Fin p) → Fin (n j) → X) : ENNReal :=
  ∏ j, IsRandomnessNecessaryADA.Plain.iid P (n j) (S j)

end HierADA


