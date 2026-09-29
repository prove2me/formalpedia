-- Prove2me | Definitions.Def_LanglandsTunnell_OctahedralDatum
-- name    : LanglandsTunnell_OctahedralDatum
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.084567+00:00
-- url     : https://prove2.me/theorems/66adbcd2-fc3a-5f8c-b3d2-091310ed9100
-- title:
--   Carriers for Langlands–Tunnell: octahedral Galois data and their Hecke eigensystems
-- statement:
--   Two structures and two propositions. `OctahedralGaloisDatum F R`, for a number field $F$ and a commutative ring $R$, packages: a type `G` carrying `Group` and `Finite` instances, a monoid homomorphism `proj : G →* Equiv.Perm (Fin 4)` together with a proof that it is surjective, and a field `attached : HeckeEigensystem F R`. Nothing in this structure relates `G` to $\mathrm{Gal}(\bar F/F)$ or relates `attached` to `proj`: `G` is an abstract finite group with a surjection onto $S_4$, and the eigensystem is free data. `TunnellOctahedralGlobal notion`, for a `CuspidalityNotion R` (the project's abstract parameter for what cuspidality means on Hecke eigensystems), asserts that for every number field $F$ and every such datum $D$ there is $\pi :$ `HeckeEigensystem F R` with `notion.IsCusp F π` and `HeckeEigensystem.AgreesAwayFromFinite π D.attached`, i.e. $\pi$ is cuspidal in the chosen sense and agrees with the attached data outside a finite set of primes.
--
--   `OctahedralGaloisDatumLinked` extends the above by data tying `attached` to an actual two-dimensional representation: `rep : G →* GL (Fin 2) R`; the requirement `rep_proj` that for each $g$, $\mathrm{proj}(g)=1$ holds exactly when the matrix of `rep g` is a scalar $c\cdot 1$ with $c \in R^\times$ (so $\ker(\mathrm{proj})$ is the locus where `rep` is scalar — only this kernel condition is imposed, not that `proj` is induced by `rep`); an arbitrary function `frob` from the height-one spectrum of $\mathcal O_F$ to `G`, otherwise unconstrained; a finite set `ramified` of primes; and the identities `attached.a v = trace (rep (frob v))`, `attached.b v = det (rep (frob v))` for every $v \notin$ `ramified`. `TunnellOctahedralGlobalLinked notion` is the same existence assertion for linked data. Both propositions are shaped as universal statements over abstract data rather than over Galois representations, so they are formally stronger and differently shaped than Tunnell's theorem.
--
--   **Relation to Mathlib.** Mathlib has no notion of automorphic representation, Hecke eigensystem or Artin representation; `HeckeEigensystem`, `CuspidalityNotion` and `AgreesAwayFromFinite` are the project's own, from the imported definition modules. Mathlib supplies only the ambient objects used here: `Equiv.Perm (Fin 4)`, `GL (Fin 2) R`, and `IsDedekindDomain.HeightOneSpectrum (𝓞 F)`.
--
--   **Where it is used.** These carriers hold the Langlands–Tunnell input to the Frey–Serre–Ribet–Wiles argument: the statement that a two-dimensional Galois representation of octahedral projective type is matched, away from finitely many places, by a cuspidal Hecke eigensystem, which is what makes the residual mod $3$ representation of a Frey curve modular. Two statement modules of the tree import this module.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_LanglandsTunnell_OctahedralDatum.lean

import Mathlib
import Definitions.Def_AutomorphicForm_HeckeEigensystem
import Definitions.Def_LanglandsTunnell_ExplicitLift

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AutomorphicForm IsDedekindDomain NumberField
open scoped MatrixGroups

namespace FLT.TunnellOctahedralGlobalCarrier

structure OctahedralGaloisDatum (F : Type) [Field F] [NumberField F]
    (R : Type*) [CommRing R] where

  G : Type

  [grp : Group G]

  [fin : Finite G]

  proj : G →* Equiv.Perm (Fin 4)

  proj_surjective : Function.Surjective proj

  attached : HeckeEigensystem F R

attribute [instance] OctahedralGaloisDatum.grp OctahedralGaloisDatum.fin

def TunnellOctahedralGlobal {R : Type*} [CommRing R] (notion : CuspidalityNotion R) : Prop :=
  ∀ (F : Type) [Field F] [NumberField F],
    ∀ D : OctahedralGaloisDatum F R,
      ∃ π : HeckeEigensystem F R,
        notion.IsCusp F π ∧ HeckeEigensystem.AgreesAwayFromFinite π D.attached

end FLT.TunnellOctahedralGlobalCarrier

namespace FLT.Qepw139bOctahedralDatumLinkedRecarve

open FLT.TunnellOctahedralGlobalCarrier

structure OctahedralGaloisDatumLinked (F : Type) [Field F] [NumberField F]
    (R : Type*) [CommRing R] extends OctahedralGaloisDatum F R where

  rep : G →* GL (Fin 2) R

  rep_proj : ∀ g : G, proj g = 1 ↔
    ∃ c : Rˣ, ((rep g : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) = (c : R) • 1

  frob : HeightOneSpectrum (𝓞 F) → G

  ramified : Finset (HeightOneSpectrum (𝓞 F))

  attached_a : ∀ v ∉ ramified,
    attached.a v = ((rep (frob v) : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R).trace

  attached_b : ∀ v ∉ ramified,
    attached.b v = ((rep (frob v) : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R).det

def TunnellOctahedralGlobalLinked {R : Type*} [CommRing R]
    (notion : CuspidalityNotion R) : Prop :=
  ∀ (F : Type) [Field F] [NumberField F],
    ∀ D : OctahedralGaloisDatumLinked F R,
      ∃ π : HeckeEigensystem F R,
        notion.IsCusp F π ∧ HeckeEigensystem.AgreesAwayFromFinite π D.attached

end FLT.Qepw139bOctahedralDatumLinkedRecarve


