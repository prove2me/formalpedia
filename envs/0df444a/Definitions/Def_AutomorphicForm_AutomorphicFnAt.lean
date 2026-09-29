-- Prove2me | Definitions.Def_AutomorphicForm_AutomorphicFnAt
-- name    : AutomorphicForm_AutomorphicFnAt
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/842a2bdc-7302-5d26-af96-a5cfe7d0116e
-- title:
--   Adelic GL2​ automorphic and cuspidal predicates at fixed measure data
-- statement:
--   Let $F$ be a number field and $G=\mathrm{GL}_2(\mathbb{A}_F)$, written `AdelicGL2 (𝓞 F) F`. A `CarrierPins F` bundle records, as plain structure fields, a $\sigma$-algebra `mS` and a measure `μ` on $G$, a subset `D ⊆ G`, a subgroup `Z` of the idele units $\mathbb{A}_F^{\times}$, a family `U` of subgroups of $G$ indexed by ideals of $\mathcal{O}_F$, a family `gen` of elements of $G$ indexed by the finite places, and a $\sigma$-algebra `nS` with a measure `ν` on $\mathbb{A}_F$. The first definition, `LsXiMemberAt`, restates the project's structure `LsXiMember` at an explicitly named measure and $\sigma$-algebra instead of an ambient `MeasureSpace` instance, for a Dedekind domain $R$ with fraction field $K$; `lsXiMemberAt_iff` unfolds it to the conjunction of two clauses: $\varphi(\gamma g)=\varphi(g)$ for all $\gamma\in\mathrm{GL}_2(K)$ embedded by $K\to\mathbb{A}_K$ and all $g$, together with $\varphi(z\cdot g)=\xi(z)\varphi(g)$ for $z\in Z$ acting through central scalars (this is `IsLsXiFunction`), and $\varphi\in L^2$ of $\mu$ restricted to $D$. Then `IsAutomorphicFnAt F pins ξ φ` is exactly `LsXiMemberAt` read at the bundle's $(mS,\mu,Z,D)$, and `IsCuspAutomorphicFnAt` adds the single further clause `IsCuspidalFn` for the bundle's $\nu$ and the upper unipotent parametrisation $x\mapsto\begin{pmatrix}1&x\\0&1\end{pmatrix}$, i.e. $\int_{\mathbb{A}_F}\varphi(u(x)g)\,d\nu(x)=0$ for every $g\in G$. These are thus only the invariance, central-character, $L^2$ and constant-term clauses: no $K$-finiteness, $\mathfrak{z}$-finiteness, smoothness or moderate-growth condition is imposed, and at an arbitrary bundle the predicates assert whatever the given data say. Four elementary facts accompany them: the zero function satisfies both predicates for every bundle and every $\xi$; the constant function $1$ satisfies `IsAutomorphicFnAt` for the trivial character as soon as $\mu(D)<\infty$; and $1$ never satisfies `IsCuspAutomorphicFnAt`, for any $\xi$, when $\nu$ is a probability measure, since its constant term is $1$.
--
--   **Relation to Mathlib.** Mathlib has no notion of automorphic form on an adelic $\mathrm{GL}_2$; the predicates, the unipotent parametrisation `unipotentGL2`, the constant term `constantTerm` and the `CarrierPins` bundle are the project's own, built on Mathlib's adele ring, Haar measure and `MemLp`. `LsXiMemberAt` is the project's `LsXiMember` with the ambient `MeasureSpace` instance replaced by an explicit measure argument.
--
--   **Where it is used.** These predicates fix the space-level vocabulary for adelic automorphic forms on $\mathrm{GL}_2$ used throughout the modularity half of the argument: further layers add, over the same bundle, the Hecke eigenvalue clauses at the level subgroups `U` and the generators `gen`, and concrete statements instantiate the bundle at the production data `productionPinsOf`, where $\mu$ is a Haar measure on $\mathrm{GL}_2(\mathbb{A}_F)$, $Z$ is all of $\mathbb{A}_F^{\times}$ and $\nu$ is a normalised conditional adelic Haar measure.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AutomorphicForm_AutomorphicFnAt.lean

import Definitions.Def_AutomorphicForm_CarrierPins
import Definitions.Def_AutomorphicForm_ConstantTerm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory
open AutomorphicForm

noncomputable section

namespace AutomorphicForm

section LsXiAt

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]

def LsXiMemberAt [MeasurableSpace (AdelicGL2 R K)] (μ : Measure (AdelicGL2 R K))
    (Z : Subgroup (AdeleRing R K)ˣ) (ξ : Z →* ℂˣ) (D : Set (AdelicGL2 R K))
    (φ : AdelicGL2 R K → ℂ) : Prop :=
  @LsXiMember R K _ _ _ _ _ Z ξ ⟨μ⟩ D φ

theorem lsXiMemberAt_iff [MeasurableSpace (AdelicGL2 R K)] (μ : Measure (AdelicGL2 R K))
    (Z : Subgroup (AdeleRing R K)ˣ) (ξ : Z →* ℂˣ) (D : Set (AdelicGL2 R K))
    (φ : AdelicGL2 R K → ℂ) :
    LsXiMemberAt R K μ Z ξ D φ ↔ IsLsXiFunction R K Z ξ φ ∧ MemLp φ 2 (μ.restrict D) := by
  letI : MeasureSpace (AdelicGL2 R K) := ⟨μ⟩
  exact ⟨fun h => ⟨h.toIsLsXiFunction, h.memLp_two⟩, fun h => ⟨h.1, h.2⟩⟩

end LsXiAt

variable (F : Type) [Field F] [NumberField F]

def IsAutomorphicFnAt (pins : CarrierPins F) (ξ : pins.Z →* ℂˣ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) : Prop :=
  @LsXiMemberAt (𝓞 F) F _ _ _ _ _ pins.mS pins.μ pins.Z ξ pins.D φ

def IsCuspAutomorphicFnAt (pins : CarrierPins F) (ξ : pins.Z →* ℂˣ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) : Prop :=
  IsAutomorphicFnAt F pins ξ φ ∧ @IsCuspidalFn _ pins.nS _ _ pins.ν unipotentGL2 φ

theorem isAutomorphicFnAt_zero (pins : CarrierPins F) (ξ : pins.Z →* ℂˣ) :
    IsAutomorphicFnAt F pins ξ (fun _ => (0 : ℂ)) := by
  letI := pins.mS; letI : MeasureSpace (AdelicGL2 (𝓞 F) F) := ⟨pins.μ⟩
  exact lsXiMember_zero (𝓞 F) F pins.Z ξ pins.D

theorem isCuspAutomorphicFnAt_zero (pins : CarrierPins F) (ξ : pins.Z →* ℂˣ) :
    IsCuspAutomorphicFnAt F pins ξ (fun _ => (0 : ℂ)) :=
  ⟨isAutomorphicFnAt_zero F pins ξ,
    fun g => by letI := pins.nS; exact constantTerm_zero pins.ν unipotentGL2 g⟩

theorem isAutomorphicFnAt_one_trivial (pins : CarrierPins F)
    (hDfin : @pins.μ pins.D < ⊤) :
    IsAutomorphicFnAt F pins (1 : pins.Z →* ℂˣ) (fun _ => (1 : ℂ)) := by
  letI := pins.mS; letI : MeasureSpace (AdelicGL2 (𝓞 F) F) := ⟨pins.μ⟩
  haveI : IsFiniteMeasure (pins.μ.restrict pins.D) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hDfin⟩
  exact ⟨⟨fun _ _ => rfl, fun _ _ => by simp⟩, memLp_const 1⟩

theorem not_isCuspAutomorphicFnAt_one (pins : CarrierPins F) (ξ : pins.Z →* ℂˣ)
    [@IsProbabilityMeasure _ pins.nS pins.ν] :
    ¬ IsCuspAutomorphicFnAt F pins ξ (fun _ => (1 : ℂ)) := by
  intro ⟨_, hcusp⟩
  letI := pins.nS
  have h1 : (1 : ℂ) = 0 := by
    have := hcusp 1; rwa [constantTerm_const] at this
  exact one_ne_zero h1

end AutomorphicForm

end


