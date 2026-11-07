-- Prove2me | Definitions.Def_GyoriLovasz_IsEssential
-- name    : GyoriLovasz_IsEssential
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:50:57.89264+00:00
-- url     : https://prove2.me/theorems/8291fd73-3a16-4deb-b835-ba6bbb253e96
-- title:
--   Flow-essential terminal
-- statement:
--   A terminal $t\in T$ is **flow-essential** (or **essential**) for a non-terminal $v\in V\setminus T$ if removing $t$ from $G$ (and from the terminal set) lowers the terminal connectivity of $v$ by exactly one:
--   $$\kappa_{G\setminus\{t\}}(v)+1=\kappa_G(v).$$
--
--   Equivalently (p.17), $t$ is the endpoint of a path in every maximum vertex-disjoint family from $v$ to $T$.
--
--   **Formalization Note** The printed form $\kappa_{G\setminus\{t\}}(v)=\kappa_G(v)-1$ is written with the $1$ on the left. In natural numbers $\kappa-1$ truncates, and the printed form would make every terminal essential for a vertex with $\kappa_G(v)=0$.
-- source:
--   Hajiaghayi, JafariRaviz, Kaviani, Mohammadkhani, Breaking the Exponential Barrier: The First Polynomial-Time Algorithm for the Győri–Lovász Theorem, arXiv:2608.30945 (held file sha256 3f80f82d3e45b364bf6e7d363e7e2291bbe55b2f994efed6cc39405149cd780e), Definition 1.1, p.6 (restated p.17)

import Mathlib
import Definitions.Def_GyoriLovasz_kappa

namespace GyoriLovasz

/-- **Flow-essential terminal.** Hajiaghayi, JafariRaviz, Kaviani, Mohammadkhani, *Breaking the Exponential Barrier*,
arXiv:2608.30945 (held file sha256 3f80f82d…780e), Definition 1.1, pp.6, 17: "We call a terminal t ∈ T flow-essential
for a non-terminal vertex v ∈ V \ T, or simply essential for v, if removing t from G reduces the terminal
connectivity of v by exactly 1, i.e., κ_{G\{t}}(v) = κ_G(v) − 1."

**Formalization Note.** Written `κ′ + 1 = κ`. In `ℕ`, the form `κ′ = κ − 1` would hold at `κ = 0` for
every terminal, which would make the Flow-Essential Assignment Condition hold on a vertex with no path
to `T`. Removing `t` removes it from the graph and from the terminal set. -/
def IsEssential {V : Type*} [DecidableEq V] (G : DG V) (T : Finset V) (v t : V) : Prop :=
  t ∈ T ∧ kappa (G.deleteVertex t) (T.erase t) v + 1 = kappa G T v

end GyoriLovasz


