-- Prove2me | Definitions.Def_NumberField_PrincipalLevel
-- name    : NumberField_PrincipalLevel
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:29.330635+00:00
-- url     : https://prove2.me/theorems/c47a843e-3ab3-5d32-b34f-3b91f9321556
-- title:
--   Weyl element and principal adelic congruence level
-- statement:
--   Throughout, $R$ is a Dedekind domain with fraction field $K$, $\mathbb{A} = \mathbb{A}_{R,K}$ is the associated adele ring, and $N$ is an ideal of $R$. Two objects are introduced. First, `weyl` is the element $w = \begin{pmatrix}0&1\\1&0\end{pmatrix}$ of $\mathrm{GL}_2(\mathbb{A})$, presented as a unit of the matrix ring with itself as two-sided inverse. Second, `principalLevel` is the subgroup
--   $$K(N) \;=\; U_1(N) \cap \mathrm{conj}_w\bigl(U_1(N)\bigr) \;\le\; \mathrm{GL}_2(\mathbb{A}),$$
--   the intersection of the level-one group $U_1(N) =$ `levelOne R K N` with its image under conjugation $g \mapsto w g w^{-1}$. Unfolding the imported notion, $g \in U_1(N)$ means that the finite-adelic part of $g$ and that of $g^{-1}$ both satisfy: all four entries are integral at every height-one prime $v$ of $R$, the lower-left entry $c$ satisfies $|c|_v \le \|N\|_v$ for all $v$, and the lower-right entry satisfies $|d-1|_v \le \|N\|_v$ for all $v$, where $\|N\|_v = \exp(-\mathrm{ord}_v(N))$ for $N \ne 0$ and $\|N\|_v = 0$ for $N = 0$; no condition is imposed at the infinite places, and none on the top row. Since conjugation by $w$ interchanges the two indices, the second factor of the intersection imposes the transposed conditions, on the upper-right and upper-left entries.
--
--   Two facts are recorded: the inclusion $K(N) \le U_1(N)$, and the membership criterion that $g \in K(N)$ exactly when $g$ lies both in $U_1(N)$ and in $w U_1(N) w^{-1}$, which restates the definition.
--
--   **Relation to Mathlib.** Mathlib has no congruence subgroups of $\mathrm{GL}_2$ over an adele ring; both the Weyl element and this principal level are the project's own, built on Mathlib's adele ring and general linear group.
--
--   **Where it is used.** The groups $K(N)$ serve as levels for the adelic test functions and automorphic objects used downstream: being contained in $U_1(N)$, they are the smaller (hence less restrictive for bi-invariance) levels over which existence statements are quantified by the ideal $N$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_NumberField_PrincipalLevel.lean

import Definitions.Def_NumberField_AdelicLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace NumberField.AdelicLevel

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]

def weyl : GL (Fin 2) (AdeleRing R K) :=
  ⟨!![0, 1; 1, 0], !![0, 1; 1, 0],
    by simp [Matrix.one_fin_two],
    by simp [Matrix.one_fin_two]⟩

variable (N : Ideal R)

def principalLevel : Subgroup (GL (Fin 2) (AdeleRing R K)) :=
  levelOne R K N ⊓ (levelOne R K N).map (MulAut.conj (weyl R K)).toMonoidHom

theorem principalLevel_le_levelOne : principalLevel R K N ≤ levelOne R K N := inf_le_left

theorem mem_principalLevel_iff {g : GL (Fin 2) (AdeleRing R K)} :
    g ∈ principalLevel R K N ↔
      g ∈ levelOne R K N ∧ g ∈ (levelOne R K N).map (MulAut.conj (weyl R K)).toMonoidHom :=
  Iff.rfl

end NumberField.AdelicLevel

end


