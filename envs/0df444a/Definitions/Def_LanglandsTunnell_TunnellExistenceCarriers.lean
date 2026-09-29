-- Prove2me | Definitions.Def_LanglandsTunnell_TunnellExistenceCarriers
-- name    : LanglandsTunnell_TunnellExistenceCarriers
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.084567+00:00
-- url     : https://prove2.me/theorems/24389565-7f67-5883-9235-4c3ab3ed3bad
-- title:
--   Carrier propositions for Tunnell's theorem on attached octahedral data
-- statement:
--   Three propositions are defined, each parametrised by one or two *cuspidality notions*: a `CuspidalityNotion R` is a structure whose single field is a family of predicates `IsCusp` on Hecke eigensystems over arbitrary number fields, so no intrinsic cuspidality is assumed; here the coefficient ring is $\mathbb{Z}[\sqrt{-2}]$. A `HeckeEigensystem F R` is a nonzero level ideal of $\mathcal{O}_F$ together with two functions $a,b$ on the finite places, and `AgreesAwayFromFinite` means the two pairs $(a_v,b_v)$ coincide outside some finite set of places.
--
--   `TunnellExistsForAttachedOctahedralData notionT` asserts: for every continuous surjective monoid homomorphism $\rho:\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})\to \mathrm{GL}_2(\mathbb{Z}/3)$ with $\det\rho(\sigma)$ equal to the mod-$3$ cyclotomic character for all $\sigma$, every linked octahedral Galois datum $D$ over $\mathbb{Q}$ (a finite group $G$ with a surjection onto $\mathrm{Perm}(\mathrm{Fin}\,4)$ whose kernel is exactly the locus where a given $G\to\mathrm{GL}_2(\mathbb{Z}[\sqrt{-2}])$ is scalar, a Frobenius assignment $v\mapsto\mathrm{frob}(v)$, a finite ramified set, and an eigensystem `attached` whose $a_v,b_v$ are the trace and determinant of $\mathrm{rep}(\mathrm{frob}(v))$ outside it), and every finite $S\subseteq\mathbb{N}$ such that $D$ is a Galois attachment of $\rho$ off $S$ (i.e. for $p\notin S$ and every Frobenius $\sigma$ at $p$, the image of $a_p$ under the ring map $\mathbb{Z}[\sqrt{-2}]\to\mathbb{Z}/3$, $\sqrt{-2}\mapsto-1$, equals $\operatorname{tr}\rho(\sigma)$), there is a `notionT`-cuspidal eigensystem over $\mathbb{Q}$ agreeing with `D.attached` away from finitely many places.
--
--   `NotionInhabitedOverRat notionD` asserts that some eigensystem over $\mathbb{Q}$ is `notionD`-cuspidal. `NotionCompatForAttachedOctahedralData notionT notionD` asserts, under the same hypotheses on $\rho,D,S$, that any `notionT`-cuspidal eigensystem agreeing almost everywhere with `D.attached` is `notionD`-cuspidal. Thus the classical theorem is reformulated at the level of Satake data $(a_v,b_v)$ up to finitely many places, with cuspidality left as a parameter.
--
--   **Relation to Mathlib.** Mathlib has no notion of Hecke eigensystem, cuspidality notion or octahedral Galois datum; these are the project's own. Mathlib supplies the ambient ingredients: `modularCyclotomicCharacter`, $\mathrm{GL}_2$, the height-one spectrum of a ring of integers, and $\mathbb{Z}[\sqrt{-2}]$ as `Zsqrtd`.
--
--   **Where it is used.** These propositions package the Langlands–Tunnell input at $p=3$: from a surjective mod-$3$ Galois representation with cyclotomic determinant, realised by a finite octahedral datum, one obtains a cuspidal Hecke eigensystem whose Satake data match the Frobenius traces and determinants almost everywhere. Combined with the realisation dictionary turning such an eigensystem into a weight-one form, and hence a weight-two form of suitable level, they feed Wiles' $3$–$5$ argument applied to the mod-$3$ representation of the Frey curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_LanglandsTunnell_TunnellExistenceCarriers.lean

import Mathlib
import Definitions.Def_LanglandsTunnell_OctahedralDatum
import Definitions.Def_LanglandsTunnell_IsGaloisAttachmentOf
import Definitions.Def_GaloisRep_ModThreeCyclotomic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AutomorphicForm WeierstrassCurve
open FLT.TunnellOctahedralGlobalCarrier FLT.Qepw139bOctahedralDatumLinkedRecarve
open scoped MatrixGroups

noncomputable section

namespace LanglandsTunnell

local notation "Γℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

def TunnellExistsForAttachedOctahedralData (notionT : CuspidalityNotion (ℤ√(-2))) : Prop :=
  ∀ ρ : Γℚ →* GL (Fin 2) (ZMod 3), Continuous ρ → Function.Surjective ρ →
    (∀ σ : Γℚ, Matrix.GeneralLinearGroup.det (ρ σ) = modThreeCyclotomicChar σ) →
    ∀ (D : OctahedralGaloisDatumLinked ℚ (ℤ√(-2))) (S : Finset ℕ),
      IsGaloisAttachmentOf ρ D.toOctahedralGaloisDatum S →
      ∃ π : HeckeEigensystem ℚ (ℤ√(-2)),
        notionT.IsCusp ℚ π ∧ HeckeEigensystem.AgreesAwayFromFinite π D.attached

def NotionInhabitedOverRat (notionD : CuspidalityNotion (ℤ√(-2))) : Prop :=
  ∃ π : HeckeEigensystem ℚ (ℤ√(-2)), notionD.IsCusp ℚ π

def NotionCompatForAttachedOctahedralData (notionT notionD : CuspidalityNotion (ℤ√(-2))) : Prop :=
  ∀ ρ : Γℚ →* GL (Fin 2) (ZMod 3), Continuous ρ → Function.Surjective ρ →
    (∀ σ : Γℚ, Matrix.GeneralLinearGroup.det (ρ σ) = modThreeCyclotomicChar σ) →
    ∀ (D : OctahedralGaloisDatumLinked ℚ (ℤ√(-2))) (S : Finset ℕ),
      IsGaloisAttachmentOf ρ D.toOctahedralGaloisDatum S →
      ∀ π : HeckeEigensystem ℚ (ℤ√(-2)),
        notionT.IsCusp ℚ π → HeckeEigensystem.AgreesAwayFromFinite π D.attached →
        notionD.IsCusp ℚ π

end LanglandsTunnell

end


