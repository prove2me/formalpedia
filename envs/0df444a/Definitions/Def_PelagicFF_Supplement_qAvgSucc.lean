-- Prove2me | Definitions.Def_PelagicFF_Supplement_qAvgSucc
-- name    : PelagicFF_Supplement_qAvgSucc
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T21:25:43.988397+00:00
-- url     : https://prove2.me/theorems/c026209e-559a-434d-962f-20db80799b50
-- title:
--   Average success probability of a quantum one-way protocol under uniform inputs
-- statement:
--   For a quantum one-way protocol $\mathcal P$ (published `PelagicFF.OneWayQProtocol`) with finite input sets $X$, $Y$ and a relation $R$, the **average success probability under the uniform input law** is
--
--   $$
--   \frac1{|X|\,|Y|}\sum_{x\in X}\sum_{y\in Y}\mathrm{succ}_{\mathcal P}(x,y),
--   $$
--
--   where $\mathrm{succ}_{\mathcal P}(x,y)$ is the probability that Bob's measurement outcome lies in $R(x,y)$.
--
--   It appears in the gate-count optimality clause of Theorem 6.2 (§6.4, p.54: protocols "with success probability at least 2/3 on uniform inputs").
-- source:
--   Anselm, Ding, Gilboa, Grewal, Optimal and Verifiable Quantum Advantages in Communication Complexity, arXiv:2610.05585 (held version, sha256 4564aef3…), §6.4, p.54

import Mathlib
import Definitions.Def_PelagicFF_OneWayQProtocol

namespace PelagicFF.Supplement

/-- Average success probability of a quantum one-way protocol under the uniform input distribution
on `X × Y`: `(|X| |Y|)⁻¹ ∑_{x,y} succProb(x, y)`.

arXiv:2610.05585 (held version, sha256 4564aef3…), §6.4, p.54: "For a protocol solving DDP_{n,d}
with success probability at least 2/3 on uniform inputs". -/
noncomputable def qAvgSucc {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z] {m : ℕ}
    (P : PelagicFF.OneWayQProtocol X Y Z m) (R : X → Y → Z → Prop) : ℝ :=
  ((Fintype.card X : ℝ) * Fintype.card Y)⁻¹ * ∑ x, ∑ y, P.succProb R x y

end PelagicFF.Supplement


