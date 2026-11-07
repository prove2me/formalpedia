-- Prove2me | Definitions.Def_GyoriLovasz_IsKTConnected
-- name    : GyoriLovasz_IsKTConnected
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:51:20.033388+00:00
-- url     : https://prove2.me/theorems/6f082d63-747e-4209-9502-b0c89e0a916d
-- title:
--   $k$-$T$-connected digraph
-- statement:
--   A directed graph $G$ with terminal set $T$ is **$k$-$T$-connected** if
--   $$\kappa_G(v)=k=|T|\quad\text{for every } v\in V\setminus T,$$
--   that is, every non-terminal has $|T|$ vertex-disjoint paths to $|T|$ distinct terminals. This is Lovász's hypothesis of $k$-connectivity to $T$.
-- source:
--   Hajiaghayi, JafariRaviz, Kaviani, Mohammadkhani, Breaking the Exponential Barrier: The First Polynomial-Time Algorithm for the Győri–Lovász Theorem, arXiv:2608.30945 (held file sha256 3f80f82d3e45b364bf6e7d363e7e2291bbe55b2f994efed6cc39405149cd780e), Definition 2.2, p.14

import Mathlib
import Definitions.Def_GyoriLovasz_kappa

namespace GyoriLovasz

/-- **`k`-`T`-connected.** Hajiaghayi, JafariRaviz, Kaviani, Mohammadkhani, *Breaking the Exponential Barrier*,
arXiv:2608.30945 (held file sha256 3f80f82d…780e), Definition 2.2, p.14: "We say that G is k-T-connected if κ_G(v) = k = |T|
for every v ∈ V \ T."

**Formalization Note.** At `T = ∅` this holds on every graph; the capacity hypothesis of `theorem_1` then
forces `V` to be empty. -/
def IsKTConnected {V : Type*} [DecidableEq V] (G : DG V) (T : Finset V) : Prop :=
  ∀ v ∈ G.verts \ T, kappa G T v = T.card

end GyoriLovasz


