-- Prove2me | Definitions.Def_TolProdTest_lambdaCc
-- name    : TolProdTest_lambdaCc
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T03:26:14.578711+00:00
-- url     : https://prove2.me/theorems/aed6e9c9-c14e-4b13-a39e-c126341a5672
-- title:
--   The operator $\Lambda_{C,c}$ of Lemma 3.3
-- statement:
--   For a coloring $C$ and a colour $c$, let $Q_{2,c}$ be the two-copy symmetric projector of block $B_c$ and $Q^{\mathrm{fine}}_{2,c}=\prod_{i\in B_c}Q_{2,i}$ the registerwise two-copy accepting projector inside $B_c$. Define
--
--   $$
--   \Lambda_{C,c}=\big(Q_{2,c}-Q^{\mathrm{fine}}_{2,c}\big)\prod_{c'\ne c}Q_{2,c'} ,
--   $$
--
--   an operator on two copies of $(\mathbb C^d)^{\otimes n}$. For an empty block both projectors are the identity, so $\Lambda_{C,c}=0$.
--
--   $\Lambda_{C,c}$ measures the acceptance lost when block $B_c$ is refined into single registers; Lemma 3.3 bounds it on average over random colorings and from below for a fixed coloring.
-- source:
--   Bao, Helsen, Nguyen, Fully tolerant product state testing and closest product state learning, arXiv:2610.01979 (version of October 1st 2026, sha256 9e43ab25…), Lemma 3.3, eq. (26), p.10

import Mathlib
import Definitions.Def_TolProdTest_symProjOn

set_option autoImplicit false

namespace TolProdTest

/-- **The operator `Λ_{C,c}`**, Bao, Helsen, Nguyen, *Fully tolerant product state testing and closest product state learning*, arXiv:2610.01979 (version of October 1st 2026, sha256 9e43ab25…), Lemma 3.3, eq. (26), p.10: "Let Q^fine_{2,c} be the registerwise
two-copy accepting projector within B_c, and define Λ_{C,c} := (Q_{2,c} − Q^fine_{2,c}) ∏_{c′≠c} Q_{2,c′}. For an
empty block both projectors are the identity, so Λ_{C,c} = 0."

Here `Q_{2,c}` is the two-copy symmetric projector of block `B_c`, `Q^fine_{2,c} = ∏_{i ∈ B_c} Q_{2,i}` the
registerwise projector inside `B_c`, and `∏_{c'≠c} Q_{2,c'}` the blockwise projector of the other colours, all
operators on the two-copy space with basis `Fin 2 → S → Fin d`. -/
noncomputable def lambdaCc {S ι : Type} [Fintype S] [DecidableEq S] [Fintype ι] [DecidableEq ι]
    (d : ℕ) (C : S → ι) (c : ι) : Matrix (Fin 2 → S → Fin d) (Fin 2 → S → Fin d) ℂ :=
  (symProjOn d C {c} 2 - symProjOn d (id : S → S) (Finset.univ.filter fun i => C i = c) 2) *
    symProjOn d C (Finset.univ.erase c) 2

end TolProdTest


