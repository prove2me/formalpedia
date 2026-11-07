-- Prove2me | Definitions.Def_GyoriLovasz_IsCritical
-- name    : GyoriLovasz_IsCritical
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:52:26.88823+00:00
-- url     : https://prove2.me/theorems/3696be85-843a-41a3-aca3-614ba57d4802
-- title:
--   Critical edge for assigning a vertex to a terminal
-- statement:
--   An edge $e$ of $G$ is **critical for assigning** a non-terminal $v$ to a terminal $t$ if $t$ is essential for $v$ in $G$ but not in $G\setminus e$. For an assignment $\varphi$, $e$ is **non-critical for $\varphi$** if it is critical for assigning no non-terminal $v$ to $\varphi(v)$.
-- source:
--   Hajiaghayi, JafariRaviz, Kaviani, Mohammadkhani, Breaking the Exponential Barrier: The First Polynomial-Time Algorithm for the Győri–Lovász Theorem, arXiv:2608.30945 (held file sha256 3f80f82d3e45b364bf6e7d363e7e2291bbe55b2f994efed6cc39405149cd780e), §4.1, p.24

import Mathlib
import Definitions.Def_GyoriLovasz_IsEssential

namespace GyoriLovasz

/-- **Critical edge.** Hajiaghayi, JafariRaviz, Kaviani, Mohammadkhani, *Breaking the Exponential Barrier*,
arXiv:2608.30945 (held file sha256 3f80f82d…780e), §4.1, p.24: "An edge e of G is critical for assigning a non-terminal v to a
terminal t if t is essential for v in G, but not in G \ e." -/
def IsCritical {V : Type*} [DecidableEq V] (G : DG V) (T : Finset V) (e : V × V) (v t : V) : Prop :=
  IsEssential G T v t ∧ ¬ IsEssential (G.deleteArc e) T v t

/-- **Non-critical for an assignment.** Hajiaghayi, JafariRaviz, Kaviani, Mohammadkhani, *Breaking the Exponential Barrier*,
arXiv:2608.30945 (held file sha256 3f80f82d…780e), §4.1, p.24: "For an assignment φ, we say e is critical for φ if it
is critical for assigning some vertex v to φ(v), and non-critical for φ otherwise." -/
def IsNonCritical {V : Type*} [DecidableEq V] (G : DG V) (T : Finset V) (e : V × V) (φ : V → V) : Prop :=
  ∀ v ∈ G.verts \ T, ¬ IsCritical G T e v (φ v)

end GyoriLovasz


