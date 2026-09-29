-- Prove2me | Definitions.Def_LocalNewvector_ConductorDatum
-- name    : LocalNewvector_ConductorDatum
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.084567+00:00
-- url     : https://prove2.me/theorems/2c86c6af-e377-5fef-a8d2-daf30a517397
-- title:
--   Fixed vectors, central characters and newvector conductors for GL2​(Qp​)
-- statement:
--   For a group $G$ acting on a complex vector space $V$ by additive maps commuting with the scalars, [`LocalNewvector.fixedSubmodule U V`](../def/LocalNewvector_ConductorDatum.html#L11) is the $\mathbb{C}$-submodule $\{v \in V : g\cdot v = v \text{ for all } g \in U\}$ attached to a subgroup $U \le G$, with membership characterised by that very condition. A group of comparison lemmas relates the congruence subgroups of the companion definition to the integral subgroup: for $R$ a commutative ring, $K$ a field and an $R$-algebra structure on $K$, the subgroups $K_0(\varpi^n)$ and $K_1(\varpi^n)$ of $\mathrm{GL}_2(K)$ — images under $\mathrm{GL}_2(R) \to \mathrm{GL}_2(K)$ of matrices whose $(1,0)$ entry lies in $(\varpi^n)$, respectively whose $(1,0)$ entry lies in $(\varpi^n)$ and whose $(1,1)$ entry is congruent to $1$ modulo $\varpi^n$ — both reduce at $n=0$ to [`LocalGL2.integralSubgroup R K`](../def/LocalLanglands_LocalHeckeInstance.html#L13), the image of $\mathrm{GL}_2(R)$, and are contained in it for every $n$; the $p$-adic specialisations $K_0(p^0)$, $K_1(p^0)$ inside $\mathrm{GL}_2(\mathbb{Q}_p)$ equal the image of $\mathrm{GL}_2(\mathbb{Z}_p)$.
--
--   For a prime $p$, `centralGL p` is the monoid homomorphism $\mathbb{Q}_p^\times \to \mathrm{GL}_2(\mathbb{Q}_p)$ sending $u$ to the scalar matrix $\mathrm{diag}(u,u)$. The predicate `IsCentralCharacterRep p V ω` says that $\mathrm{diag}(u,u)$ acts on every $v \in V$ as multiplication by $\omega(u) \in \mathbb{C}^\times$; such an $\omega$ is shown to be unique as soon as $V$ contains a nonzero vector. The predicate `HasNewvectorConductor p V c` is the conjunction: the fixed submodule of $K_1(p^c)$ in $V$ is nonzero, and the fixed submodule of $K_1(p^m)$ is zero for every $m < c$; such a $c$ is unique. Note that only nonvanishing, not one-dimensionality, is required at level $c$. `IsIrreducibleGLRep p V` asserts that $V \neq 0$ and every $\mathbb{C}$-submodule stable under all of $\mathrm{GL}_2(\mathbb{Q}_p)$ is $\bot$ or $\top$, with no smoothness clause. Finally `HasFiniteLevelFixed p V` asserts that for every $n$ the fixed submodule of [`FLT.SmoothVectors.gl2CongruenceSubgroup p n`](../def/RepTheory_GL2CongruenceSubgroup.html#L181) (the elements $g$ with all entries of $g-1$ and of $g^{-1}-1$ of $p$-adic absolute value at most $p^{-n}$) is a finite-dimensional $\mathbb{C}$-vector space.
--
--   **Relation to Mathlib.** Mathlib organises representations through `Representation`/`Rep`; here the representation is a bare `DistribMulAction` of $\mathrm{GL}_2(\mathbb{Q}_p)$ on a $\mathbb{C}$-module, and the submodule of $U$-fixed vectors, the central-character predicate, algebraic irreducibility and the newvector conductor exponent are the project's own notions.
--
--   **Where it is used.** These are the local definitions in which statements about newvectors, central characters and conductor exponents at $p$ for representations of $\mathrm{GL}_2(\mathbb{Q}_p)$ are phrased, and they are used by the parts of the development that keep track of levels and local conductors.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_LocalNewvector_ConductorDatum.lean

import Definitions.Def_LocalNewvector_CongruenceSubgroupK1
import Definitions.Def_RepTheory_GL2CongruenceSubgroup
import Definitions.Def_LocalLanglands_LocalHeckeInstance

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

namespace LocalNewvector

def fixedSubmodule {G : Type*} [Group G] (U : Subgroup G) (V : Type*) [AddCommGroup V]
    [Module ℂ V] [DistribMulAction G V] [SMulCommClass G ℂ V] : Submodule ℂ V where
  carrier := {v | ∀ g ∈ U, g • v = v}
  add_mem' := by
    intro v w hv hw g hg
    rw [smul_add, hv g hg, hw g hg]
  zero_mem' := by
    intro g _
    exact smul_zero g
  smul_mem' := by
    intro c v hv g hg
    rw [smul_comm, hv g hg]

theorem mem_fixedSubmodule_iff {G : Type*} [Group G] {U : Subgroup G} {V : Type*}
    [AddCommGroup V] [Module ℂ V] [DistribMulAction G V] [SMulCommClass G ℂ V] {v : V} :
    v ∈ fixedSubmodule U V ↔ ∀ g ∈ U, g • v = v :=
  Iff.rfl

section IntegralSubgroupSeam

variable {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K]

theorem congruenceK0_zero_eq_integralSubgroup (ϖ : R) :
    congruenceK0 (K := K) ϖ 0 = LocalGL2.integralSubgroup R K :=
  congruenceK0_zero ϖ

theorem congruenceK1_zero_eq_integralSubgroup (ϖ : R) :
    congruenceK1 (K := K) ϖ 0 = LocalGL2.integralSubgroup R K :=
  congruenceK1_zero ϖ

theorem congruenceK0_le_integralSubgroup (ϖ : R) (n : ℕ) :
    congruenceK0 (K := K) ϖ n ≤ LocalGL2.integralSubgroup R K := by
  rintro x ⟨y, rfl, _⟩
  exact ⟨y, rfl⟩

theorem congruenceK1_le_integralSubgroup (ϖ : R) (n : ℕ) :
    congruenceK1 (K := K) ϖ n ≤ LocalGL2.integralSubgroup R K :=
  (congruenceK1_le_congruenceK0 _ _).trans (congruenceK0_le_integralSubgroup ϖ n)

end IntegralSubgroupSeam

section Padic

variable (p : ℕ) [Fact p.Prime]

theorem padicK0_zero_eq_integralSubgroup :
    padicK0 p 0 = LocalGL2.integralSubgroup ℤ_[p] ℚ_[p] :=
  congruenceK0_zero_eq_integralSubgroup (p : ℤ_[p])

theorem padicK1_zero_eq_integralSubgroup :
    padicK1 p 0 = LocalGL2.integralSubgroup ℤ_[p] ℚ_[p] :=
  congruenceK1_zero_eq_integralSubgroup (p : ℤ_[p])

def centralGL : ℚ_[p]ˣ →* GL (Fin 2) ℚ_[p] :=
  Units.map (algebraMap ℚ_[p] (Matrix (Fin 2) (Fin 2) ℚ_[p])).toMonoidHom

def IsCentralCharacterRep (V : Type*) [AddCommGroup V] [Module ℂ V]
    [DistribMulAction (GL (Fin 2) ℚ_[p]) V] (ω : ℚ_[p]ˣ →* ℂˣ) : Prop :=
  ∀ (u : ℚ_[p]ˣ) (v : V), centralGL p u • v = (ω u : ℂ) • v

theorem centralCharacterRep_unique {V : Type*} [AddCommGroup V] [Module ℂ V]
    [DistribMulAction (GL (Fin 2) ℚ_[p]) V] (hV : ∃ v : V, v ≠ 0)
    {ω ω' : ℚ_[p]ˣ →* ℂˣ} (hω : IsCentralCharacterRep p V ω)
    (hω' : IsCentralCharacterRep p V ω') : ω = ω' := by
  obtain ⟨v, hv0⟩ := hV
  have key : ∀ u : ℚ_[p]ˣ, (ω u : ℂ) = (ω' u : ℂ) := by
    intro u
    by_contra hne
    have hcne : (ω u : ℂ) - (ω' u : ℂ) ≠ 0 := sub_ne_zero.mpr hne
    have h3 : ((ω u : ℂ) - (ω' u : ℂ)) • v = 0 := by
      rw [sub_smul, ← hω u v, ← hω' u v, sub_self]
    exact hv0 (by
      calc v = ((ω u : ℂ) - (ω' u : ℂ))⁻¹ • (((ω u : ℂ) - (ω' u : ℂ)) • v) := by
            rw [smul_smul, inv_mul_cancel₀ hcne, one_smul]
        _ = 0 := by rw [h3, smul_zero])
  exact MonoidHom.ext fun u => Units.ext (key u)

def HasNewvectorConductor (V : Type*) [AddCommGroup V] [Module ℂ V]
    [DistribMulAction (GL (Fin 2) ℚ_[p]) V] [SMulCommClass (GL (Fin 2) ℚ_[p]) ℂ V]
    (c : ℕ) : Prop :=
  fixedSubmodule (padicK1 p c) V ≠ ⊥ ∧ ∀ m < c, fixedSubmodule (padicK1 p m) V = ⊥

theorem hasNewvectorConductor_unique {V : Type*} [AddCommGroup V] [Module ℂ V]
    [DistribMulAction (GL (Fin 2) ℚ_[p]) V] [SMulCommClass (GL (Fin 2) ℚ_[p]) ℂ V]
    {c c' : ℕ} (h : HasNewvectorConductor p V c) (h' : HasNewvectorConductor p V c') :
    c = c' := by
  rcases lt_trichotomy c c' with hlt | heq | hgt
  · exact absurd (h'.2 c hlt) h.1
  · exact heq
  · exact absurd (h.2 c' hgt) h'.1

def IsIrreducibleGLRep (V : Type*) [AddCommGroup V] [Module ℂ V]
    [DistribMulAction (GL (Fin 2) ℚ_[p]) V] : Prop :=
  (∃ v : V, v ≠ 0) ∧
  ∀ W : Submodule ℂ V,
    (∀ g : GL (Fin 2) ℚ_[p], ∀ v ∈ W, g • v ∈ W) → W = ⊥ ∨ W = ⊤

def HasFiniteLevelFixed (V : Type*) [AddCommGroup V] [Module ℂ V]
    [DistribMulAction (GL (Fin 2) ℚ_[p]) V] [SMulCommClass (GL (Fin 2) ℚ_[p]) ℂ V] : Prop :=
  ∀ n : ℕ, Module.Finite ℂ (fixedSubmodule (FLT.SmoothVectors.gl2CongruenceSubgroup p n) V)

end Padic

end LocalNewvector


