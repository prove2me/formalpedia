-- Prove2me | Definitions.Def_PunctSketch_coinProb
-- name    : PunctSketch_coinProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:41:35.108602+00:00
-- url     : https://prove2.me/theorems/a89fdc4d-50f2-4319-aaa6-77c931bf83f5
-- title:
--   Probability under uniform coins
-- statement:
--   For a finite coin space $\Omega$ and an event $A$, this is the fraction $|\{\omega\in\Omega : A(\omega)\}|/|\Omega|$, the probability of $A$ under uniform coins.
--
--   **Formalization Note** On an empty space this reads $0/0=0$; every statement that uses it has a nonempty space by construction or assumes one.
-- source:
--   Çekirge, Chakrabarti, Dutta, McGregor, Vinayak, Puncturable Graph Sketches and the Complexity of Distributed Vertex Connectivity, STOC 2027 submission (manuscript sha256 a630f88815653b5f1b35579cbfa2100b617a4d540f009489027b8c55f65e1a2c), §2, p.5 (PDF p.6)

import Mathlib

namespace PunctSketch

open Classical in
/-- **Probability under uniform coins.** Çekirge, Chakrabarti, Dutta, McGregor, Vinayak, *Puncturable Graph Sketches and the Complexity of Distributed Vertex Connectivity*, STOC 2027 submission (manuscript sha256 a630f888…), §2, p.5.

`coinProb A` is the fraction of the points of the finite coin space `Ω` that satisfy `A`, that is
the probability of `A` when the coins are uniform on `Ω`.

**Formalization Note.** On an empty `Ω` this is `0/0 = 0`, so every statement that uses it either
has a nonempty coin space by construction or assumes one. -/
noncomputable def coinProb {Ω : Type*} [Fintype Ω] (A : Ω → Prop) : ℝ :=
  ((Finset.univ.filter A).card : ℝ) / (Fintype.card Ω : ℝ)

end PunctSketch


