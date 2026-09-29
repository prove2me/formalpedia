-- Prove2me | Definitions.Def_AutomorphicForm_UnitFactorizableOfType
-- name    : AutomorphicForm_UnitFactorizableOfType
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/3a874d6c-a09d-53d2-a5d8-df741c23c998
-- title:
--   Unit-factorizable adelic test functions of prescribed archimedean type
-- statement:
--   Throughout, $K$ is a number field with ring of integers $\mathcal{O}_K$, and functions are complex-valued functions on $\mathrm{GL}_2$ of the adele ring of $K$. For a family of archimedean types `tys : ArchTypeFamily K`, an open-level datum given by a subgroup $U \le \mathrm{GL}_2(\mathbb{A}_K)$, and a finite set $S$ of height-one primes of $\mathcal{O}_K$, the predicate `IsUnitFactorizableOfTypeAt K tys U S f` is defined as the conjunction of two conditions: `IsUnitFactorizableAt K U S f` and `IsArchBiFinite K tys f`. The first, unfolded, says that $f(ug) = f(g)$ and $f(gu) = f(g)$ for all $u \in U$ and all $g$, and that there exist an archimedean factor $f_\infty$ on $\mathrm{GL}_2$ of the infinite adeles, a finite factor $f_{\mathrm{fin}}$ on $\mathrm{GL}_2$ of the finite adeles, and local functions $f_v$ on $\mathrm{GL}_2(K_v)$ such that $f_\infty$ is an archimedean test factor, $f_{\mathrm{fin}}$ a finite test factor, each $f_v$ for $v \in S$ is locally constant with compact support, $f_{\mathrm{fin}}(h) = \prod_{v \in S} f_v(h_v)$ whenever $h_v$ lies in the local integral set (entries of $h_v$ and of $h_v^{-1}$ in $\mathcal{O}_v$) for every $v \notin S$, $f_{\mathrm{fin}}(h) = 0$ as soon as $h_v$ fails to be integral at some $v \notin S$, and $f(g) = f_\infty(g_\infty)\, f_{\mathrm{fin}}(g_{\mathrm{fin}})$. The second condition is the predicate `IsArchBiFinite` attached to the family `tys`, which constrains the behaviour of $f$ at the infinite places.
--
--   The accompanying lemmas are the two projections, the consequence that such an $f$ is a factorizable test function, antitonicity in the level ($U \le V$ and the property at $V$ give it at $U$), monotonicity in the type family along `ArchTypeFamily.IsContainedIn`, a criterion upgrading `IsUnitFactorizableAt` to the typed version from a factorization $f(g) = f_\infty(g_\infty) f_{\mathrm{fin}}(g_{\mathrm{fin}})$ whose archimedean factor satisfies `IsArchFactorBiFinite`, the fact that the zero function qualifies for every `tys`, $U$ and $S$, and one nonzero instance: for an archimedean test factor $f_\infty$ satisfying `IsArchFactorBiFinite` for `tys` and a level $U$ all of whose elements have trivial archimedean part and integral finite part, the function $g \mapsto f_\infty(g_\infty)\,\mathbf{1}_{\mathrm{unitFinSet}}(g_{\mathrm{fin}})$ qualifies, for every finite $S$; here `unitFinSet K` is the set of finite adelic matrices integral, together with their inverses, at every finite place.
--
--   **Relation to Mathlib.** Mathlib has no notion of adelic test function or of archimedean type for $\mathrm{GL}_2$ over a number field; these predicates are the project's own, formulated over Mathlib's adele ring, finite adele ring and height-one spectrum.
--
--   **Where it is used.** These predicates belong to the adelic automorphic-forms layer of the development, where test functions of prescribed level, ramification set and archimedean type are used to realise Hecke eigensystems on isotypic cuspidal spaces.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AutomorphicForm_UnitFactorizableOfType.lean

import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain

namespace AutomorphicForm

section TierRefined

variable (K : Type) [Field K] [NumberField K]

def IsUnitFactorizableOfTypeAt (tys : ArchTypeFamily K)
    (U : Subgroup (GL (Fin 2) (AdeleRing (𝓞 K) K))) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) : Prop :=
  IsUnitFactorizableAt K U S f ∧ IsArchBiFinite K tys f

variable {K}

theorem IsUnitFactorizableOfTypeAt.isUnitFactorizableAt {tys : ArchTypeFamily K}
    {U : Subgroup (GL (Fin 2) (AdeleRing (𝓞 K) K))} {S : Finset (HeightOneSpectrum (𝓞 K))}
    {f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ} (hf : IsUnitFactorizableOfTypeAt K tys U S f) :
    IsUnitFactorizableAt K U S f :=
  hf.1

theorem IsUnitFactorizableOfTypeAt.isArchBiFinite {tys : ArchTypeFamily K}
    {U : Subgroup (GL (Fin 2) (AdeleRing (𝓞 K) K))} {S : Finset (HeightOneSpectrum (𝓞 K))}
    {f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ} (hf : IsUnitFactorizableOfTypeAt K tys U S f) :
    IsArchBiFinite K tys f :=
  hf.2

theorem IsUnitFactorizableOfTypeAt.isFactorizableTestFn {tys : ArchTypeFamily K}
    {U : Subgroup (GL (Fin 2) (AdeleRing (𝓞 K) K))} {S : Finset (HeightOneSpectrum (𝓞 K))}
    {f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ} (hf : IsUnitFactorizableOfTypeAt K tys U S f) :
    IsFactorizableTestFn K f :=
  hf.1.isFactorizableTestFn K

theorem IsUnitFactorizableOfTypeAt.mono {tys : ArchTypeFamily K}
    {U V : Subgroup (GL (Fin 2) (AdeleRing (𝓞 K) K))} (hUV : U ≤ V)
    {S : Finset (HeightOneSpectrum (𝓞 K))} {f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ}
    (hf : IsUnitFactorizableOfTypeAt K tys V S f) : IsUnitFactorizableOfTypeAt K tys U S f :=
  ⟨hf.1.mono K hUV, hf.2⟩

theorem IsUnitFactorizableOfTypeAt.mono_type {tys tys' : ArchTypeFamily K}
    (h : tys.IsContainedIn K tys') {U : Subgroup (GL (Fin 2) (AdeleRing (𝓞 K) K))}
    {S : Finset (HeightOneSpectrum (𝓞 K))} {f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ}
    (hf : IsUnitFactorizableOfTypeAt K tys U S f) : IsUnitFactorizableOfTypeAt K tys' U S f :=
  ⟨hf.1, hf.2.mono K h⟩

theorem IsUnitFactorizableAt.isUnitFactorizableOfTypeAt_of_factorization {tys : ArchTypeFamily K}
    {U : Subgroup (GL (Fin 2) (AdeleRing (𝓞 K) K))} {S : Finset (HeightOneSpectrum (𝓞 K))}
    {f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ} (hf : IsUnitFactorizableAt K U S f)
    {fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ} {ff : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ}
    (hfac : ∀ g, f g = fa (AdelicLevel.glArch (𝓞 K) K g) * ff (AdelicLevel.glFin (𝓞 K) K g))
    (hfa : IsArchFactorBiFinite K tys fa) : IsUnitFactorizableOfTypeAt K tys U S f :=
  ⟨hf, IsArchBiFinite.of_factorization K hfac hfa⟩

variable (K)

theorem isUnitFactorizableOfTypeAt_zero (tys : ArchTypeFamily K)
    (U : Subgroup (GL (Fin 2) (AdeleRing (𝓞 K) K))) (S : Finset (HeightOneSpectrum (𝓞 K))) :
    IsUnitFactorizableOfTypeAt K tys U S fun _ => 0 :=
  ⟨isUnitFactorizableAt_zero K U S, isArchBiFinite_zero K tys⟩

theorem isUnitFactorizableOfTypeAt_mul_indicator_unitFinSet (tys : ArchTypeFamily K)
    {fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ} (hfa : IsArchTestFactor K fa)
    (hfa' : IsArchFactorBiFinite K tys fa) {U : Subgroup (GL (Fin 2) (AdeleRing (𝓞 K) K))}
    (hU : IsIntegralLevel K U) (S : Finset (HeightOneSpectrum (𝓞 K))) :
    IsUnitFactorizableOfTypeAt K tys U S fun g => fa (AdelicLevel.glArch (𝓞 K) K g) *
      (unitFinSet K).indicator (fun _ => (1 : ℂ)) (AdelicLevel.glFin (𝓞 K) K g) :=
  (isUnitFactorizableAt_mul_indicator_unitFinSet K hfa hU S).isUnitFactorizableOfTypeAt_of_factorization
    (fun _ => rfl) hfa'

end TierRefined

end AutomorphicForm


