-- Prove2me | Definitions.Def_BorderD4_evalAt
-- name    : BorderD4_evalAt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T15:59:02.431343+00:00
-- url     : https://prove2.me/theorems/326c8a84-1f5b-488e-9b60-816ac08a4ffe
-- title:
--   Substitutions $p(u,\varphi)$, $b+(u,g)$ and $g(\varepsilon^e,y)$
-- statement:
--   For $T\subseteq[N]$, $u=x_T$ and a tuple $g=(g_a)_{a\notin T}$, the tuple $(u,g)$ has $a$-th entry $x_a$ if $a\in T$ and $g_a$ if $a\notin T$, and $b+(u,g)$ adds the point $b\in F^N$. This item defines these tuples over $F[[\varepsilon,u]]$ (`freeDep`, `shifted`) and over $F[[u]]$ (`uShift`), the substitution $p\mapsto p(y)$ of a tuple into $p\in F[[\varepsilon]][x]$ (`evalAt`), and the substitution $g\mapsto g(\varepsilon^e,y)$ of Lemma 6.11 (`expandEval`).
-- source:
--   A. Dey, P. Dutta, Z. Guo, An Exponential Top Fan-In Hierarchy for Border Depth-4 Circuits, STOC 2027 submission (manuscript sha256 518aaf99…), §6.2, p.52; Lemma 6.11, p.57; Lemma 6.20, p.75

import Mathlib
import Definitions.Def_BorderD4_IsEpsUnit
set_option autoImplicit false

open MvPolynomial
open scoped PowerSeries

namespace BorderD4

section

variable {F σ : Type*} [Field F] [DecidableEq σ]

/-- The inclusion `F[[ε]] → F[[ε, u]]`. -/
noncomputable def constEmb (F τ : Type*) [Field F] : F⟦X⟧ →+* EpsSeries F τ :=
  PowerSeries.map MvPowerSeries.C

/-- The tuple `(u, g)` with `u = x_T`: its `a`-th entry is `x_a` if `a ∈ T` and `g_a` if `a ∉ T`.
Source: Dey, Dutta, Guo, An Exponential Top Fan-In Hierarchy for Border Depth-4 Circuits, STOC 2027 submission (manuscript sha256 518aaf99…), §6.2, p.52. -/
noncomputable def freeDep (T : Finset σ) (g : {a // a ∉ T} → EpsSeries F T) (i : σ) : EpsSeries F T :=
  if h : i ∈ T then PowerSeries.C (MvPowerSeries.X (⟨i, h⟩ : T)) else g ⟨i, h⟩

/-- The tuple `b + (u, g)` with `b ∈ F^σ`. Source: Dey, Dutta, Guo, An Exponential Top Fan-In Hierarchy for Border Depth-4 Circuits, STOC 2027 submission (manuscript sha256 518aaf99…), §6.2, p.52. -/
noncomputable def shifted (T : Finset σ) (b : σ → F) (g : {a // a ∉ T} → EpsSeries F T) (i : σ) :
    EpsSeries F T :=
  constEmb F T (PowerSeries.C (b i)) + freeDep T g i

/-- The substitution `p ↦ p(y)` of a tuple `y` over `F[[ε, u]]` into `p ∈ F[[ε]][x]`. With `y = freeDep T φ` this
is `p(u, φ)` of Theorem 6.7. Source: Dey, Dutta, Guo, An Exponential Top Fan-In Hierarchy for Border Depth-4 Circuits, STOC 2027 submission (manuscript sha256 518aaf99…), §6.2, p.52. -/
noncomputable def evalAt (T : Finset σ) (y : σ → EpsSeries F T) :
    MvPolynomial σ F⟦X⟧ →+* EpsSeries F T :=
  eval₂Hom (constEmb F T) y

/-- The substitution `g ↦ g(ε^e, y)` of Lemma 6.11: `a(ε) ↦ a(ε^e)` on each coefficient and `x ↦ y`.
Source: Dey, Dutta, Guo, An Exponential Top Fan-In Hierarchy for Border Depth-4 Circuits, STOC 2027 submission (manuscript sha256 518aaf99…), Lemma 6.11, p.57. -/
noncomputable def expandEval (T : Finset σ) (e : ℕ) (he : e ≠ 0) (y : σ → EpsSeries F T) :
    MvPolynomial σ F⟦X⟧ →+* EpsSeries F T :=
  eval₂Hom
    (((PowerSeries.expand e he : EpsSeries F T →ₐ[MvPowerSeries T F] EpsSeries F T) :
      EpsSeries F T →+* EpsSeries F T).comp (constEmb F T)) y

/-- The tuple `b + (u, g)` with `g_a ∈ F[[u]]`. Source: Dey, Dutta, Guo, An Exponential Top Fan-In Hierarchy for Border Depth-4 Circuits, STOC 2027 submission (manuscript sha256 518aaf99…), §6.2, p.52; Lemma 6.20, p.75. -/
noncomputable def uShift (T : Finset σ) (b : σ → F) (g : {a // a ∉ T} → MvPowerSeries T F) (i : σ) :
    MvPowerSeries T F :=
  MvPowerSeries.C (b i) + if h : i ∈ T then MvPowerSeries.X (⟨i, h⟩ : T) else g ⟨i, h⟩

end

end BorderD4


