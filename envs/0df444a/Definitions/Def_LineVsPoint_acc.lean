-- Prove2me | Definitions.Def_LineVsPoint_acc
-- name    : LineVsPoint_acc
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T08:05:02.43723+00:00
-- url     : https://prove2.me/theorems/41fdfb3c-ec5d-4147-9a20-048b94a7203b
-- title:
--   Acceptance probability $\mathrm{Acc}(f,\{P_L\})$ of the line–versus–point test
-- statement:
--   Let $\mathbb F$ be a finite field, $f:\mathbb F^m\to\mathbb F$ a point table and $\{P_L\}$ a degree-$d$ line table. The line–versus–point test samples an incident pair $(x,L)$, with $x\in\mathbb F^m$ and $L$ an affine line containing $x$, uniformly at random, and accepts iff $P_L(x)=f(x)$. Its **acceptance probability** is
--
--   $$
--   \mathrm{Acc}(f,\{P_L\}) := \Pr_{x\in\mathbb F^m,\ L\ni x}\bigl[P_L(x)=f(x)\bigr]
--   =\frac{\#\{(x,L): x\in L,\ P_L(x)=f(x)\}}{\#\{(x,L): x\in L\}} .
--   $$
--
--   This is the quantity whose size the soundness theorems relate to the agreement of $f$ with a global low-degree polynomial.
--
--   **Formalization Note** The definition is literally the ratio of accepted incident pairs to all incident pairs, lines being sets (`Line F m`).
-- source:
--   Dao, Kominers, Thaler, Zheng, Cube-Root Soundness Is Optimal for the Line–versus–Point Test (manuscript, sha256 328a8943…), §1.1, p.4

import Definitions.Def_LineVsPoint_LineTable

set_option autoImplicit false

namespace LineVsPoint

open Classical in
/-- The **acceptance probability** of the line–versus–point test: Dao, Kominers, Thaler, Zheng,
*Cube-Root Soundness Is Optimal for the Line–versus–Point Test* (manuscript, sha256 328a8943…),
§1.1, p.4: "The test samples an incident pair `(x, L)` uniformly at random, where `x ∈ F^m_q` and
`L ∈ L_{q,m}` such that `x ∈ L`, and accepts if and only if `P_L(x) = f(x)`",
`Acc(f, {P_L}) := Pr_{x ∈ F^m_q, L ∋ x}[P_L(x) = f(x)]`.

**Formalization Note.** Literally the number of accepted incident pairs `(x, L)` divided by the
number of incident pairs, with `L` ranging over lines as sets (`Line F m`). -/
noncomputable def acc {F : Type*} [Field F] [Fintype F] {m d : ℕ} (f : (Fin m → F) → F)
    (P : LineTable F m d) : ℝ :=
  ((Finset.univ.filter fun xL : (Fin m → F) × Line F m => Accepted f P xL.1 xL.2).card : ℝ) /
    ((Finset.univ.filter fun xL : (Fin m → F) × Line F m => xL.1 ∈ xL.2.carrier).card : ℝ)

end LineVsPoint


