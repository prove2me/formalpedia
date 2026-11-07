-- Prove2me | Definitions.Def_QLocalCert_TreeEQ
-- name    : QLocalCert_TreeEQ
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:41:07.517255+00:00
-- url     : https://prove2.me/theorems/b789a809-4667-4bc2-8c96-d47c6365ae3a
-- title:
--   The graph properties $\mathrm{TreeEQ}_\mu$ and $\mathrm{Tree}_\mu$
-- statement:
--   For $\mu\ge1$,
--   $$
--   \mathrm{TreeEQ}_\mu=\{T: T\cong T^{\mathrm{tr}}_{N,\mu}(z,z)\text{ for some even }N\ge8\text{ and balanced }z\in\{0,1\}^N\},
--   $$
--   $$
--   \mathrm{Tree}_\mu=\{T: T\cong T^{\mathrm{tr}}_{N,\mu}(z,z')\text{ for some even }N\ge8\text{ and balanced }z,z'\in\{0,1\}^N\}.
--   $$
--   A graph belongs to $\mathrm{TreeEQ}_\mu$ when it has the prescribed tree shape and its two encoded strings coincide. Both classes are closed under isomorphism, so they are graph properties.
--
--   These are the property of the main theorem (Theorem 1) and the property certified structurally by Lemma 27.
--
--   **Formalization Note** Membership of a graph on $n$ nodes is the existence of a graph isomorphism `≃g` to the tree.
-- source:
--   Jauregui, Miyamoto, Quantum Advantage in Local Certification of Graph Properties, STOC 2027 submission (manuscript sha256 b707143b1ab5511bef4c2b77e1b803f28b32cced25a008516898fd11d28c0451), §4, p.37

import Mathlib
import Definitions.Def_QLocalCert_Ttr

set_option autoImplicit false

namespace QLocalCert

/-- The graph property **TreeEQµ** (§4, p.37): "For any fixed positive integer µ ≥ 1, we define the
graph property TreeEQµ as follows: TreeEQµ := {T : T ≅ T^tr_{N,µ}(z, z) for some even N ≥ 8 and z
of weight N/2}."

Source: B. Jauregui, M. Miyamoto, *Quantum Advantage in Local Certification of Graph Properties*,
STOC 2027 submission (manuscript sha256 b707143b…0c51), §4, p.37.

**Formalization Note.** A graph on `Fin n` has the property when it is isomorphic (`≃g`) to
`T^tr_{N,µ}(z, z)` for some even `N ≥ 8` and some balanced `z ∈ {0,1}^N`; the property is closed
under isomorphism by construction. -/
def TreeEQ (μ : ℕ) {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∃ N : ℕ, Even N ∧ 8 ≤ N ∧ ∃ z : Fin N → Bool, Balanced z ∧ Nonempty (G ≃g Ttr N μ z z)

/-- The graph property **Treeµ** (§4, p.37): "Treeµ := {T : T ≅ T^tr_{N,µ}(z, z′) for some even
N ≥ 8, z, z′ ∈ {0, 1}^N with wt(z) = wt(z′) = N/2}."

Source: as `TreeEQ`, p.37. -/
def TreeP (μ : ℕ) {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∃ N : ℕ, Even N ∧ 8 ≤ N ∧ ∃ z z' : Fin N → Bool, Balanced z ∧ Balanced z' ∧
    Nonempty (G ≃g Ttr N μ z z')

end QLocalCert


