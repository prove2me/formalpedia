-- Prove2me | Definitions.Def_NSWBetter_largeGoods
-- name    : NSWBetter_largeGoods
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:54:53.838641+00:00
-- url     : https://prove2.me/theorems/29862e54-6576-4c0a-b91a-fdbc345e6741
-- title:
--   The set $L$ of large goods of an identical-valuation instance
-- statement:
--   For an instance with $\Delta$ identical agents and valuation $v$, the set of **large goods** $L=\{g: v(g)>\Delta\mu/(\Delta-\ell)\}$ (Definition 3.2); all other goods are **small**.
-- source:
--   Viswanathan, A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations, arXiv:2607.13340 (held version, sha256 08811cb468c2df39231dca4222c5af94163587c7c83e205e50bbf0b91fc1deb3), Definition 3.2, p.11

import Mathlib
import Definitions.Def_NSWBetter_thr
import Definitions.Def_NSWBetter_vals

namespace NSWBetter

open Classical in
/-- **The set L of large goods.**
Viswanathan, *A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations*, arXiv:2607.13340 (held version, sha256 08811cb4…), Definition 3.2, p.11.

`largeGoods Δ v = {g | v(g) > thr Δ (vals v)}`: the goods whose value exceeds `v(G\L)/(Δ − ℓ)`. Its complement is the set of small goods.

**Formalization Note.** By Definition 3.2 and Observation 3.3 this is exactly the set `L`, and its cardinality is `largeCount Δ (vals v)`. -/
noncomputable def largeGoods (Δ : ℕ) {m : ℕ} (v : Fin m → ℝ) : Finset (Fin m) :=
  Finset.univ.filter fun g => thr Δ (vals v) < v g

end NSWBetter


