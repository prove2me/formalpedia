-- Prove2me | Definitions.Def_LanglandsTunnell_DeltaLift
-- name    : LanglandsTunnell_DeltaLift
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.084567+00:00
-- url     : https://prove2.me/theorems/4ae1a9ec-66f6-5164-a3b5-138b643ce91b
-- title:
--   Adelic lift of the discriminant form and its Hecke eigensystem
-- statement:
--   Working over $F=\mathbb{Q}$, this module sets up the weight-$12$ level-one discriminant cusp form as data for adelic $\mathrm{GL}_2$. First, `deltaArchLift` sends $h\in\mathrm{GL}_2(\mathbb{R})$ to $\bigl(\Delta\mid_{12}h\bigr)(i)\cdot(\det h)^{-5}$, where $\Delta$ is Mathlib's `CuspForm.discriminant`, the slash is the weight-$12$ slash action and $i$ is the distinguished point of the upper half-plane; the factor $(\det h)^{-5}$ is the normalisation by $(k-2)/2$ at $k=12$. Next, `ratArchGL2` extracts from $g\in\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$ its archimedean part, takes the component at the default infinite place of $\mathbb{Q}$, and transports it entrywise along the identification of the completion at that (real) place with $\mathbb{R}$. The predicate `HasDeltaDecomp g` asserts the existence of $\gamma\in\mathrm{GL}_2(\mathbb{Q})$ and adelic $h,u$ with: $u$ lying in the level-$\top$ compact subgroup of `productionPinsCompact ℚ`, that is in $\mathrm{levelOne}(\mathbb{Z},\mathbb{Q},\top)$ intersected with the kernel of the archimedean projection; $h$ trivial at all finite places; $\mathrm{ratArchGL2}\,h$ of positive determinant; and $g=\gamma\cdot h\cdot u$ (with $\gamma$ viewed adelically). Then `deltaLift g` is $\mathrm{deltaArchLift}(\mathrm{ratArchGL2}\,h)$ for a chosen such $h$ when `HasDeltaDecomp g` holds, and $0$ otherwise; it is thus defined through a choice of decomposition, no invariance being asserted here.
--
--   On the Hecke side, `deltaRawTable` is the eigensystem over $\mathbb{Q}$ with values in $\mathbb{C}$ of level the unit ideal $\top$, with $a(v)$ the coefficient of index $N v=\lvert\mathcal{O}/v\rvert$ in the $q$-expansion of $\Delta$ times $(N v)^{-5}$, i.e. $\tau(Nv)\,(Nv)^{-5}$, and $b(v)=1$. Finally `deltaLiftSystem` is its image under `ofRawCentral`, so it has the same level and the same $a$, and central table $b(v)=N v$; two lemmas record that its level is $\top$ and that applying `toRawCentral` returns `deltaRawTable`.
--
--   **Relation to Mathlib.** The modular input ($\Delta$ as `CuspForm.discriminant`, the slash action, `UpperHalfPlane.qExpansion`) is Mathlib's; the adelic and Hecke-eigensystem vocabulary (`CarrierPins`, `productionPinsCompact`, `AdelicLevel.glFin`/`glArch`, `globalPoints`, `HeckeEigensystem` with its `toRawCentral`/`ofRawCentral` renormalisation) is the project's own.
--
--   **Where it is used.** These definitions provide the concrete level-one example feeding the project's notion of arithmetic cuspidal realisation of a Hecke eigensystem over $\mathbb{Q}$ at the compact pins, the framework in which automorphic forms on $\mathrm{GL}_2$ of the adeles are handled in the Langlands–Tunnell input to the modularity argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_LanglandsTunnell_DeltaLift.lean

import Definitions.Def_AutomorphicForm_ProductionPinsCompact
import Definitions.Def_AutomorphicForm_ArithCuspRealization

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Matrix AutomorphicForm AutomorphicForm.HeckeEigensystem
open scoped ModularForm MatrixGroups

namespace LanglandsTunnell

def deltaArchLift (h : GL (Fin 2) ℝ) : ℂ :=
  ((⇑CuspForm.discriminant) ∣[(12 : ℤ)] h) UpperHalfPlane.I * ((h.det.val : ℝ) : ℂ) ^ (-5 : ℤ)

def ratArchGL2 (g : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) : GL (Fin 2) ℝ :=
  GeneralLinearGroup.map
    (InfinitePlace.Completion.ringEquivRealOfIsReal
      (IsTotallyReal.isReal (default : InfinitePlace ℚ))).toRingHom
    (AdelicLevel.archComponent ℚ default (AdelicLevel.glArch (𝓞 ℚ) ℚ g))

def HasDeltaDecomp (g : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) : Prop :=
  ∃ (γ : GL (Fin 2) ℚ) (h u : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)),
    u ∈ (productionPinsCompact ℚ).U ⊤ ∧ AdelicLevel.glFin (𝓞 ℚ) ℚ h = 1 ∧
    ratArchGL2 h ∈ GLPos (Fin 2) ℝ ∧ g = globalPoints (𝓞 ℚ) ℚ γ * h * u

open scoped Classical in

def deltaLift (g : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) : ℂ :=
  if H : HasDeltaDecomp g then deltaArchLift (ratArchGL2 H.choose_spec.choose) else 0

def deltaRawTable : HeckeEigensystem ℚ ℂ where
  level := ⊤
  level_ne_bot := top_ne_bot
  a := fun v => (UpperHalfPlane.qExpansion 1 (⇑CuspForm.discriminant)).coeff
      (Ideal.absNorm v.asIdeal) * (cNorm v) ^ (-5 : ℤ)
  b := fun _ => 1

def deltaLiftSystem : HeckeEigensystem ℚ ℂ := ofRawCentral deltaRawTable

@[simp] theorem deltaLiftSystem_level : deltaLiftSystem.level = ⊤ := rfl

@[simp] theorem deltaLiftSystem_toRawCentral : deltaLiftSystem.toRawCentral = deltaRawTable :=
  HeckeEigensystem.toRawCentral_ofRawCentral deltaRawTable

end LanglandsTunnell


