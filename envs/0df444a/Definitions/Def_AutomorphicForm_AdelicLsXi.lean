-- Prove2me | Definitions.Def_AutomorphicForm_AdelicLsXi
-- name    : AutomorphicForm_AdelicLsXi
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/52e34c02-f9ec-5842-b15a-35c317522914
-- title:
--   Carriers for the adelic GL2​ automorphic L2 space Ls​(ξ)
-- statement:
--   Throughout, $R$ is a Dedekind domain with fraction field $K$ (the typeclasses `IsDedekindDomain`, `IsFractionRing` are assumed), and `AdelicGL2 R K` abbreviates $\mathrm{GL}_2(\mathbb{A}_K)$, i.e. `Matrix.GeneralLinearGroup (Fin 2) (AdeleRing R K)`. Two group homomorphisms into it are named: `globalPoints`, the entrywise image of $\mathrm{GL}_2(K)$ under the structure map $K \to \mathbb{A}_K$, and `centralScalar`, the embedding $\mathbb{A}_K^\times \to \mathrm{GL}_2(\mathbb{A}_K)$ sending $z$ to the scalar matrix $z\cdot I$. Three predicates on a character $\chi : \mathbb{A}_K^\times \to \mathbb{C}^\times$ (a bare monoid homomorphism; no continuity is imposed) are recorded: `IsIdeleClassChar`, that $\chi$ kills the principal ideles, $\chi(u)=1$ for all $u \in K^\times$; `IsUnitaryChar`, that $\lVert \chi(x)\rVert = 1$ for all $x$; and, relative to a subgroup $Z \le \mathbb{A}_K^\times$ with a character $\xi : Z \to \mathbb{C}^\times$, `SquaresToXi`, that $\chi(z)^2 = \xi(z)$ for all $z \in Z$. Finally `chiDet χ` is the function $g \mapsto \chi(\det g)$ on $\mathrm{GL}_2(\mathbb{A}_K)$.
--
--   The two main carriers concern a function $\varphi : \mathrm{GL}_2(\mathbb{A}_K) \to \mathbb{C}$. The structure `IsLsXiFunction R K Z ξ φ` has exactly two fields: left invariance, $\varphi(\gamma g) = \varphi(g)$ for all $\gamma \in \mathrm{GL}_2(K)$ (embedded by `globalPoints`) and all $g$; and the central transformation law $\varphi(z\cdot I\,g) = \xi(z)\varphi(g)$ for $z \in Z$. The structure `LsXiMember R K Z ξ D φ` extends this by a single further field, `memLp_two`: $\varphi \in L^2$ for the measure `volume` restricted to a set $D \subseteq \mathrm{GL}_2(\mathbb{A}_K)$. Here the measure comes from an assumed `MeasureSpace` instance on $\mathrm{GL}_2(\mathbb{A}_K)$ — no Haar property is required — and $D$ is an arbitrary set, not required to be a fundamental set for $\mathrm{GL}_2(K)Z$. No smoothness, $K$-finiteness, moderate growth or cuspidality condition appears. The lemmas `isLsXiFunction_zero` and `lsXiMember_zero` check that the zero function satisfies both.
--
--   **Relation to Mathlib.** Mathlib supplies the ingredients (`AdeleRing`, `Matrix.GeneralLinearGroup`, `MemLp`) but has no notion of automorphic forms on adelic $\mathrm{GL}_2$; the predicates and structures here are the project's own.
--
--   **Where it is used.** This is the carrier layer for the adelic automorphic $L^2$ space $L_s(\xi)$ on $\mathrm{GL}_2$, on which the project's automorphic and cuspidal realisation notions are built, in the direction of the Jacquet–Langlands and Langlands–Tunnell input to the proof. The module is imported very widely in the development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AutomorphicForm_AdelicLsXi.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open NumberField MeasureTheory Matrix

noncomputable section

namespace AutomorphicForm

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]

abbrev AdelicGL2 : Type _ :=
  Matrix.GeneralLinearGroup (Fin 2) (AdeleRing R K)

def globalPoints : Matrix.GeneralLinearGroup (Fin 2) K →* AdelicGL2 R K :=
  Matrix.GeneralLinearGroup.map (algebraMap K (AdeleRing R K))

def centralScalar : (AdeleRing R K)ˣ →* AdelicGL2 R K :=
  Matrix.GeneralLinearGroup.scalar (Fin 2)

def IsIdeleClassChar (χ : (AdeleRing R K)ˣ →* ℂˣ) : Prop :=
  ∀ u : Kˣ, χ (Units.map (algebraMap K (AdeleRing R K)) u) = 1

def IsUnitaryChar (χ : (AdeleRing R K)ˣ →* ℂˣ) : Prop :=
  ∀ x : (AdeleRing R K)ˣ, ‖((χ x : ℂˣ) : ℂ)‖ = 1

def SquaresToXi (Z : Subgroup (AdeleRing R K)ˣ) (ξ : Z →* ℂˣ)
    (χ : (AdeleRing R K)ˣ →* ℂˣ) : Prop :=
  ∀ z : Z, χ (z : (AdeleRing R K)ˣ) ^ 2 = ξ z

variable (Z : Subgroup (AdeleRing R K)ˣ) (ξ : Z →* ℂˣ)

structure IsLsXiFunction (φ : AdelicGL2 R K → ℂ) : Prop where
  left_invariant : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) K) (g : AdelicGL2 R K),
    φ (globalPoints R K γ * g) = φ g
  central_transform : ∀ (z : Z) (g : AdelicGL2 R K),
    φ (centralScalar R K (z : (AdeleRing R K)ˣ) * g) = ((ξ z : ℂˣ) : ℂ) * φ g

theorem isLsXiFunction_zero : IsLsXiFunction R K Z ξ (fun _ => (0 : ℂ)) :=
  ⟨fun _ _ => rfl, fun _ _ => by simp⟩

variable [MeasureSpace (AdelicGL2 R K)] (D : Set (AdelicGL2 R K))

structure LsXiMember (φ : AdelicGL2 R K → ℂ) : Prop extends IsLsXiFunction R K Z ξ φ where
  memLp_two : MemLp φ 2 ((volume : Measure (AdelicGL2 R K)).restrict D)

theorem lsXiMember_zero : LsXiMember R K Z ξ D (fun _ => (0 : ℂ)) :=
  ⟨isLsXiFunction_zero R K Z ξ, MemLp.zero'⟩

def chiDet (χ : (AdeleRing R K)ˣ →* ℂˣ) : AdelicGL2 R K → ℂ :=
  fun g => ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)

end AutomorphicForm

end


