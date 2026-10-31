-- Prove2me | Definitions.Def_FASTournament_FASMengerian
-- name    : FASTournament_FASMengerian
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:33:16.093236+00:00
-- url     : https://prove2.me/theorems/f434903e-6ad5-48e7-8539-377e6883975d
-- title:
--   FAS Mengerian (FASM) digraph
-- statement:
--   Let $N$ be the **FAS-arc incidence matrix** of a digraph $G=(V,A)$: one row for each FAS $F$ of $G$, one column for each arc $e$, with entry $1$ if $e\in F$ and $0$ otherwise. $G$ is **FAS Mengerian (FASM)** if the system
--   $$
--   Nx\ge\mathbf 1,\qquad x\ge\mathbf 0
--   $$
--   is totally dual integral. By the Edmonds–Giles theorem this is equivalent to $\lambda_w(G)=\mu_w(G)$ for every $w\in\mathbb Z_+^A$.
--
--   **Formalization Note** Rows are indexed by all FASs; non-minimal rows are dominated by minimal ones and do not change the notion. If $G$ is acyclic, $\emptyset$ is an FAS, its row reads $0\ge 1$, and the system is TDI vacuously.
-- source:
--   Chen, Ding, Zang & Zhao, Packing Feedback Arc Sets in Tournaments Exactly, Math. Oper. Res. (2024), doi:10.1287/moor.2023.1352, p.3

import Mathlib
import Definitions.Def_FASTournament_Arc
import Definitions.Def_FASTournament_IsFAS
import Definitions.Def_FASTournament_IsTDI

open Classical

namespace FASTournament

/-- **FAS Mengerian (FASM) digraph.**
Chen, Ding, Zang & Zhao, *Packing Feedback Arc Sets in Tournaments Exactly*,
Math. Oper. Res. (2024), doi:10.1287/moor.2023.1352, p.3: "We use N to denote the FAS-arc incidence matrix of G. … We say … that G is FAS
Mengerian (FASM) if Nx ≥ 1, x ≥ 0 is a TDI system."

`N` has one row per FAS `F` of `G` and one column per arc `e`, with entry `1` if `e ∈ F` and `0`
otherwise; `G` is FAS Mengerian if `Nx ≥ 1, x ≥ 0` is TDI.

**Formalization Note.** The rows are all FASs (not only the minimal ones), as in "the FAS-arc
incidence matrix"; a non-minimal row is dominated by a minimal one and the two choices give the
same notion. If `G` is acyclic, `∅` is an FAS, its row reads `0 ≥ 1`, the primal is infeasible
and the system is TDI vacuously. Finite types are made `Fintype` classically. -/
def FASMengerian {V : Type*} [Finite V] (G : Digraph V) : Prop :=
  letI : Fintype V := Fintype.ofFinite V
  IsTDI (fun (F : {F : Finset (Arc G) // IsFAS G F}) (e : Arc G) => if e ∈ F.1 then (1 : ℤ) else 0)
    (fun _ => 1)

end FASTournament


