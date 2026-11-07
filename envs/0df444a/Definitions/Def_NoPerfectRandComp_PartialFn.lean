-- Prove2me | Definitions.Def_NoPerfectRandComp_PartialFn
-- name    : NoPerfectRandComp_PartialFn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:42:15.532205+00:00
-- url     : https://prove2.me/theorems/f171a950-3363-44dc-a5a0-a33364ad5823
-- title:
--   Possibly partial Boolean functions, total functions and block composition $f\circ g$
-- statement:
--   A **possibly partial Boolean function** on a coordinate set $\iota$ is a map $f : \mathrm{Dom}(f) \to \{0,1\}$ with $\mathrm{Dom}(f) \subseteq \{0,1\}^\iota$; $f$ is **total** when $\mathrm{Dom}(f) = \{0,1\}^\iota$.
--
--   For $f$ on $\iota$ and $g$ on $\kappa$, the **block composition** $f \circ g$ is the function on $\{0,1\}^{\iota\times\kappa}$ obtained by feeding the $|\iota|$ disjoint blocks $x_{i,\cdot} = (x_{(i,j)})_{j\in\kappa}$ into copies of $g$:
--   $$
--   (f\circ g)(x) = f\big((g(x_{i,\cdot}))_{i\in\iota}\big),
--   $$
--   defined on the inputs whose every block lies in $\mathrm{Dom}(g)$ and whose vector of inner values lies in $\mathrm{Dom}(f)$.
--
--   These are the objects of every query-complexity statement in the mission; the inner composition theorem is stated for partial $f$ and $g$.
--
--   **Formalization Note** A partial function is a pair (domain set, value function); the value function is defined everywhere, but only its values on the domain carry meaning, and every claim about error, bias or value quantifies over the domain only. The value of the composition is the published block composition `OAI.Paper320.compose`.
-- source:
--   Meiburg, No Perfect Randomized Composition, arXiv:2610.31638 (held version, sha256 5122a74a…), §2.1, p.4

import Mathlib
import Definitions.Def_OAI_Combinatorics_Sensitivity_Composition

namespace NoPerfectRandComp

/-- A possibly partial Boolean function on the coordinate set `ι` (Meiburg, *No Perfect Randomized Composition*, arXiv:2610.31638 (held version, sha256 5122a74a…aeae3), §2.1, p.4):
`f : Dom(f) → {0,1}` with `Dom(f) ⊆ {0,1}^ι`.

**Formalization Note** A partial function is a pair (domain set, value function). The value
function is defined everywhere, but only its restriction to `dom` carries meaning: every claim in
this development about error, bias or value of a partial function quantifies over `dom` only. -/
structure PartialFn (ι : Type) where
  /-- the domain `Dom(f) ⊆ {0,1}^ι` -/
  dom : Set (ι → Bool)
  /-- the value `f(x)`; meaningful for `x ∈ dom` only -/
  val : (ι → Bool) → Bool

/-- A total Boolean function, `Dom(f) = {0,1}^ι` (Meiburg, *No Perfect Randomized Composition*, arXiv:2610.31638 (held version, sha256 5122a74a…aeae3), §2.1, p.4). -/
def PartialFn.total {ι : Type} (f : (ι → Bool) → Bool) : PartialFn ι :=
  ⟨Set.univ, f⟩

/-- Block composition `f ∘ g` of possibly partial Boolean functions (Meiburg, *No Perfect Randomized Composition*, arXiv:2610.31638 (held version, sha256 5122a74a…aeae3), §2.1, p.4):
feed the disjoint blocks `x(i, ·)` into copies of `g` and the vector of their values into `f`.
An input is in the domain when every block lies in `Dom(g)` and the vector of inner values lies
in `Dom(f)`. The value is the published block composition `OAI.Paper320.compose`. -/
def PartialFn.comp {ι κ : Type} (f : PartialFn ι) (g : PartialFn κ) : PartialFn (ι × κ) where
  dom := {x | (∀ i, (fun j => x (i, j)) ∈ g.dom) ∧
    (fun i => g.val (fun j => x (i, j))) ∈ f.dom}
  val := OAI.Paper320.compose f.val g.val

end NoPerfectRandComp


