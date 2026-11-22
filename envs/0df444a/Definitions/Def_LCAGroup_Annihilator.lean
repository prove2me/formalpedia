-- Prove2me | Definitions.Def_LCAGroup_Annihilator
-- name    : LCAGroup_Annihilator
-- status  : Definition
-- author  : @emmgaml
-- created : 2026-11-22T10:48:50.891792+00:00
-- url     : https://prove2.me/theorems/4798e7c9-0f91-4d9a-ad1b-351391c615e7
-- title:
--   The annihilator $H^\perp\subseteq\widehat G$ of a subgroup $H$ of an abelian topological group $G$, as a subgroup of the Pontryagin dual
-- statement:
--   This is the **annihilator** (orthogonal) of a subgroup in the Pontryagin dual group.
--
--   Let $G$ be an abelian topological group and let $\widehat G$ be its Pontryagin dual: the group of continuous characters $\chi\colon G\to U(1)$, with pointwise multiplication and the compact-open topology. For a subgroup $H\subseteq G$, the annihilator of $H$ in $\widehat G$ is
--   $$H^\perp=\{\chi\in\widehat G:\ \chi(h)=1\ \text{for all }h\in H\}.$$
--   It is a subgroup of $\widehat G$ (the kernel of the restriction homomorphism $\widehat G\to\widehat H$, $\chi\mapsto\chi|_H$), and it is closed in $\widehat G$.
--
--   For a Hausdorff locally compact abelian group $G$ and a closed subgroup $H$ the annihilator expresses the duality between subgroups and quotients: $\widehat{G/H}\cong H^\perp$, $\widehat G/H^\perp\cong\widehat H$ and $H^{\perp\perp}=H$ (Lemma D.1.4.6 of the source). The source uses it to define the good subgroups and structural pairs $(\Gamma,k)$ behind the Schwartz–Bruhat space $\mathcal S(G)$ (Definition D.1.5.1) and to normalise the Haar measure on $H^\perp$ in the Poisson summation formula (Situation D.1.2.6).
--
--   **Formalization Note.** `LCAGroup.annihilator H` is a `Subgroup (PontryaginDual G)`, where `PontryaginDual G` is Mathlib's dual group (continuous homomorphisms $G\to$ `Circle` with the compact-open topology); groups are written multiplicatively. Membership unfolds by `LCAGroup.mem_annihilator_iff`: $\chi\in H^\perp\iff\forall x\in H,\ \chi(x)=1$. The definition is made for an arbitrary subgroup of an arbitrary abelian topological group; closedness and local compactness are hypotheses of the theorems, not of the definition. Its underlying set is the set-valued `MasulloGRH.annihilator H` of the platform definition `MasulloGRH_SchwartzBruhat`; the present definition adds the subgroup structure, which is needed to form the quotient group $\widehat G/H^\perp$ and to regard $H^\perp$ as a topological group.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 758, Definition D.1.4.5, eq. (D.1.4.6)

import Mathlib

/-!
# The annihilator of a subgroup in the Pontryagin dual

Source: A. M. Masullo, *The Music of the Primes* (draft of 20 November 2026), Appendix D,
Definition D.1.4.5, eq. (D.1.4.6), p. 758.

For an abelian topological group `G` with Pontryagin dual `Ĝ = PontryaginDual G` (the continuous
characters `G → Circle` with the compact-open topology) and a subgroup `H` of `G`, the annihilator
`H^⊥ = {χ ∈ Ĝ : χ(H) = 1}` is a subgroup of `Ĝ`.  It is the kernel of the restriction map
`Ĝ → Ĥ`; it is closed in `Ĝ`.
-/

namespace LCAGroup

variable {G : Type*} [CommGroup G] [TopologicalSpace G]

/-- The annihilator `H^⊥ = {χ ∈ Ĝ : χ(H) = 1}` of a subgroup `H` of `G`, as a subgroup of the
Pontryagin dual `Ĝ = PontryaginDual G` (Definition D.1.4.5, eq. (D.1.4.6)). -/
def annihilator (H : Subgroup G) : Subgroup (PontryaginDual G) where
  carrier := {χ | ∀ x ∈ H, χ x = 1}
  one_mem' := fun _ _ => rfl
  mul_mem' := fun {χ ψ} hχ hψ x hx => by
    show χ x * ψ x = 1
    rw [hχ x hx, hψ x hx, mul_one]
  inv_mem' := fun {χ} hχ x hx => by
    show (χ x)⁻¹ = 1
    rw [hχ x hx, inv_one]

/-- A character lies in `H^⊥` exactly when it is trivial on `H`. -/
@[simp]
theorem mem_annihilator_iff (H : Subgroup G) (χ : PontryaginDual G) :
    χ ∈ annihilator H ↔ ∀ x ∈ H, χ x = 1 :=
  Iff.rfl

end LCAGroup


