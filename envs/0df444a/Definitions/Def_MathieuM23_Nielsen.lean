-- Prove2me | Definitions.Def_MathieuM23_Nielsen
-- name    : MathieuM23_Nielsen
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-04T14:02:49.877615+00:00
-- url     : https://prove2.me/theorems/8e4fa0f7-4b26-4118-a7cb-7934a294d976
-- title:
--   The Nielsen class of $(2,23A,23B)$ in $M_{23}$
-- statement:
--   Let $C_1, C_2, C_3$ be the $M_{23}$-conjugacy classes of $g_1, g_2, g_3$ respectively. In the source's labelling these are the classes $2$, $23A$, $23B$. Define
--
--   $$\Sigma_c=\{(h_1,h_2,h_3)\in C_1\times C_2\times C_3:\ h_1h_2h_3=1,\ \langle h_1,h_2,h_3\rangle=M_{23}\},$$
--
--   and let the **Nielsen class** $\mathrm{Ni}_c$ be the set of orbits of $\Sigma_c$ under simultaneous conjugation $(h_1,h_2,h_3)\mapsto(kh_1k^{-1},kh_2k^{-1},kh_3k^{-1})$, $k\in M_{23}$.
--
--   By the Riemann existence theorem, $\mathrm{Ni}_c$ is in bijection with the $M_{23}$-covers of $\mathbb{P}^1_{\mathbb{C}}$ branched over three points with local monodromy $(2,23A,23B)$.
--
--   **Formalization Note** The classes are defined through the representatives $g_1,g_2,g_3$, and orbits are represented as subsets of the set of triples.
-- source:
--   X. Huang, B. Jackson, K.-H. Lee, B. Poonen, R. Pries, S. Zhang, *The Mathieu group M23 is a Galois group over Q*, arXiv:2608.08538v1 (2026), https://arxiv.org/abs/2608.08538, p. 4, §2.3 (definitions of $\bar\Sigma_c$, $\Sigma_c$, $\mathrm{Ni}_c$) and §3 (the classes $2, 23A, 23B$ and the triple $(g_1,g_2,g_3)\in\Sigma_c$)

import Definitions.Def_MathieuM23_Group

/-!
# The Nielsen class of the class triple `(2, 23A, 23B)` of `M₂₃` (§2.3 and §3)

The classes `C₁ = 2`, `C₂ = 23A`, `C₃ = 23B` are the `M₂₃`-conjugacy classes of
`g₁`, `g₂`, `g₃` respectively.
-/

namespace MathieuM23

/-- Simultaneous conjugation of a triple of permutations by `k`. -/
def conjTriple (k : Equiv.Perm (Fin 23))
    (x : Equiv.Perm (Fin 23) × Equiv.Perm (Fin 23) × Equiv.Perm (Fin 23)) :
    Equiv.Perm (Fin 23) × Equiv.Perm (Fin 23) × Equiv.Perm (Fin 23) :=
  (k * x.1 * k⁻¹, k * x.2.1 * k⁻¹, k * x.2.2 * k⁻¹)

/-- `Σ_c`: triples `(h₁, h₂, h₃) ∈ C₁ × C₂ × C₃` with `h₁ h₂ h₃ = 1` that generate `M₂₃`. -/
def sigmaC : Set (Equiv.Perm (Fin 23) × Equiv.Perm (Fin 23) × Equiv.Perm (Fin 23)) :=
  {x | x.1 ∈ classIn g₁ ∧ x.2.1 ∈ classIn g₂ ∧ x.2.2 ∈ classIn g₃ ∧
    x.1 * x.2.1 * x.2.2 = 1 ∧ Subgroup.closure {x.1, x.2.1, x.2.2} = M23}

/-- The Nielsen class `Ni_c = Inn(M₂₃) \ Σ_c`, as the set of orbits of `Σ_c` under simultaneous
conjugation by elements of `M₂₃`. -/
def nielsenClass :
    Set (Set (Equiv.Perm (Fin 23) × Equiv.Perm (Fin 23) × Equiv.Perm (Fin 23))) :=
  (fun x => {y | ∃ k ∈ M23, y = conjTriple k x}) '' sigmaC

end MathieuM23


