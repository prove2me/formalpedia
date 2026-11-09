-- Prove2me | Definitions.Def_AbelianCayleyHDX_Phi
-- name    : AbelianCayleyHDX_Phi
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:34:39.138227+00:00
-- url     : https://prove2.me/theorems/1e8f9d73-d787-4119-9129-5ec6d77529e7
-- title:
--   The trace map $\Phi(u)(p,x) = \mathrm{Tr}(p\,u(x))$
-- statement:
--   For $u : V_0 \to F$, $\Phi(u) \in \mathbb F_2^{\Omega}$ is
--   $$\Phi(u)(p, x) = \mathrm{Tr}\big(p\, u(x)\big), \qquad (p, x) \in F^\times \times V_0,$$
--   where $\mathrm{Tr} = \mathrm{Tr}_{F/\mathbb F_2}$ is the field trace.
--
--   **Formalization Note** $F$ is given its $\mathbb F_2$-algebra structure (which exists exactly in characteristic two and is unique), and $\mathrm{Tr}$ is `Algebra.trace (ZMod 2) F`.
-- source:
--   Songtao Mao, Abelian Cayley High-Dimensional Expanders with Polylogarithmic Degree, arXiv:2609.08937 (held version, sha256 6f5b0daa…75ba), Lemma 3.6, p.13

import Mathlib
import Definitions.Def_AbelianCayleyHDX_Omega

namespace AbelianCayleyHDX

/-- **The map `Φ`** (Mao, *Abelian Cayley High-Dimensional Expanders with Polylogarithmic Degree*, arXiv:2609.08937 (held version, sha256 6f5b0daa…75ba), Lemma 3.6, p.13): `Φ(u)(p, x) = Tr(p u(x))` for `u : V₀ → F`, where
`Tr = Tr_{F/𝔽₂}` is the field trace.

**Formalization Note** `F` is an `𝔽₂`-algebra (`[Algebra (ZMod 2) F]`, which holds exactly when
`F` has characteristic two, and is then unique); `Tr` is `Algebra.trace (ZMod 2) F`. -/
noncomputable def Phi {t : ℕ} {F : Type*} [Field F] [Algebra (ZMod 2) F] (u : (Fin t → F) → F) :
    Omega F t → ZMod 2 :=
  fun c => Algebra.trace (ZMod 2) F ((c.1 : F) * u c.2)

end AbelianCayleyHDX


