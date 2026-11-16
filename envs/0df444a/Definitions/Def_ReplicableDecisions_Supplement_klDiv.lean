-- Prove2me | Definitions.Def_ReplicableDecisions_Supplement_klDiv
-- name    : ReplicableDecisions_Supplement_klDiv
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:00:26.118807+00:00
-- url     : https://prove2.me/theorems/e0e2854a-317a-40ff-8042-5cf59edc84b5
-- title:
--   Relative entropy $\mathrm{KL}(P\|Q)$ of finite laws
-- statement:
--   For two laws $P,Q$ on a finite set,
--   $$\mathrm{KL}(P\|Q)=\sum_z P(z)\log\frac{P(z)}{Q(z)},$$
--   with the natural logarithm.
--
--   It enters the comparable-information condition (4.18) of the ordered product family, $\mathrm{KL}(Q_i^-\|Q_i^+)\le A\lambda$.
--
--   **Formalization Note** The formula is used only for strictly positive laws, where every term is defined.
-- source:
--   Chen, Replicable Decisions in Finite Experiments: A Chain Converse and Its Limits, STOC 2027 submission (sha256 52d181db50a1641806d046c9e7d92377e64271681f0fc36c7e6be16d6dabb868), (4.18), p.21 (PDF p.23)

import Mathlib

namespace ReplicableDecisions.Supplement

/-- **Relative entropy** `KL(P ∥ Q) = ∑_z P(z) log(P(z)/Q(z))` (natural logarithm) between two laws
on a finite set. Chen, *Replicable Decisions in Finite Experiments*, STOC 2027 submission
(sha256 52d181db…), (4.18), p.21 (PDF p.23), and the proof of Theorem 4.2, p.19 (PDF p.21).

**Formalization Note.** The formula is the textbook one; it is used only for strictly positive laws
(the ordered product family of §4.2), where every term is defined. "Logarithms are natural unless a
base is specified" (p.9). -/
noncomputable def klDiv {α : Type*} [Fintype α] (P Q : α → ℝ) : ℝ :=
  ∑ z, P z * Real.log (P z / Q z)

end ReplicableDecisions.Supplement


