-- Prove2me | Definitions.Def_GoodQLTC_dir
-- name    : GoodQLTC_dir
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:40:15.447559+00:00
-- url     : https://prove2.me/theorems/94765206-bd56-40e7-b748-837ef6f077fe
-- title:
--   Direction, codirection and dimension of a face; the order of $C_t$
-- statement:
--   For $t\ge1$, $C_t=\{0,1,\star\}^{[t]}$ is ordered by $c\le d$ iff for every $i$ either $c_i=d_i$ or $d_i=\star$. For a labelling $\phi:X\to C_t$ and a face $f$,
--   $$
--   \mathrm{dir}(f)=\{i:\phi_i(f)=\star\},\qquad \mathrm{codir}(f)=[t]\setminus\mathrm{dir}(f),\qquad \dim f=|\mathrm{dir}(f)|.
--   $$
--   The module also defines the bit $\phi_i(f)\in\{0,1\}$ for $i\in\mathrm{codir}(f)$.
--
--   **Formalization Note** Words are functions `Fin t → Option Bool` (`none` = $\star$).
-- source:
--   Gay, Jeronimo, Asymptotically Good Quantum Locally Testable Codes, arXiv:2609.20780 (held version, sha256 04ad03ca…), §4.1, p.15 (PDF p.18)

import Mathlib

namespace GoodQLTC

/-- The order of the cube poset `C_t := {0, 1, ⋆}^{[t]}`, Gay–Jeronimo, arXiv:2609.20780 (held
version), §4.1, p.15: `c ≤ d` iff for every `i ∈ [t]`, either `c_i = d_i` or `d_i = ⋆`.

**Formalization Note.** A word of `C_t` is a function `Fin t → Option Bool`: `none` is `⋆`,
`some false` is `0`, `some true` is `1`; `[t]` is `Fin t`. -/
def cubeLe {t : ℕ} (c d : Fin t → Option Bool) : Prop :=
  ∀ i, c i = d i ∨ d i = none

/-- The **direction** (type) `dir(f) := {i ∈ [t] : ϕ_i(f) = ⋆}` of a face `f` of a complex with
labelling `ϕ : X → C_t` (arXiv:2609.20780, §4.1, p.15). -/
def dir {X : Type} {t : ℕ} (φ : X → Fin t → Option Bool) (f : X) : Finset (Fin t) :=
  Finset.univ.filter fun i => φ f i = none

/-- The **codirection** `codir(f) := [t] ∖ dir(f)` (arXiv:2609.20780, §4.1, p.15). -/
def codir {X : Type} {t : ℕ} (φ : X → Fin t → Option Bool) (f : X) : Finset (Fin t) :=
  Finset.univ.filter fun i => φ f i ≠ none

/-- The **dimension** `dim f := |dir(f)|` (arXiv:2609.20780, §4.1, p.15). -/
def fdim {X : Type} {t : ℕ} (φ : X → Fin t → Option Bool) (f : X) : ℕ :=
  (dir φ f).card

/-- The bit `ϕ_i(f) ∈ {0, 1}` of a face in a fixed direction `i ∈ codir(f)` (`false` = 0,
`true` = 1). **Formalization Note.** Only used for `i ∈ codir(f)`; the value `false` at `⋆` is a
placeholder. -/
def bit {X : Type} {t : ℕ} (φ : X → Fin t → Option Bool) (f : X) (i : Fin t) : Bool :=
  (φ f i).getD false

end GoodQLTC


