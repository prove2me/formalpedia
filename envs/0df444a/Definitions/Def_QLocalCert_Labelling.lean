-- Prove2me | Definitions.Def_QLocalCert_Labelling
-- name    : QLocalCert_Labelling
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:41:27.817911+00:00
-- url     : https://prove2.me/theorems/dfecf4ce-8b87-4adf-aa3f-fadee6746217
-- title:
--   Side-compatible identifier and port assignments for the trees $T^{\mathrm{tr}}_{N,\mu}(z,z')$
-- statement:
--   In the proof of Theorem 29 all trees $T^{\mathrm{tr}}_{N,\mu}(z,z')$ (for balanced $z,z'$) receive identifiers and ports so that the two sides can be exchanged: "we can keep the identifiers of $h_L$, $h_R$ and all $w_j$ fixed … within each side, enumerate the vertices other than its root in a fixed order determined by the encoded string … choose the internal port numbering of each side in the same way, and keep the ports along the central path, including its attachments to $h_L$ and $h_R$, fixed. Consequently, whenever the same string occurs on the same side of two instances, that side has identical identifiers and ports."
--
--   A **labelling** assigns to every pair $(z,z')$ an instance on the common node set $\{0,\dots,n-1\}$, together with fixed nodes $w_1,\dots,w_{2\mu}$ and fixed node sets for the left and right sides. It is **side-compatible** when, for balanced strings,
--   1. the left and right node sets are disjoint;
--   2. the instance for $(z,z')$ is isomorphic to $T^{\mathrm{tr}}_{N,\mu}(z,z')$ by an isomorphism sending $w_j$ to the fixed node $w_j$, the left side (with $h_L$) into the left node set and the right side (with $h_R$) into the right node set;
--   3. the identifiers and port numberings of the left-side nodes depend only on $z$;
--   4. those of the right-side nodes depend only on $z'$;
--   5. those of $w_1,\dots,w_{2\mu}$ depend on neither string.
--
--   This is the assignment under which Claim C holds.
--
--   **Formalization Note** Port numberings are compared as the neighbour lists in port order.
-- source:
--   Jauregui, Miyamoto, Quantum Advantage in Local Certification of Graph Properties, STOC 2027 submission (manuscript sha256 b707143b1ab5511bef4c2b77e1b803f28b32cced25a008516898fd11d28c0451), proof of Theorem 29, p.42 (with footnote 3)

import Mathlib
import Definitions.Def_QLocalCert_Instance
import Definitions.Def_QLocalCert_Ttr

set_option autoImplicit false

namespace QLocalCert

/-- An assignment of instances (identifiers and ports) to all trees `T^tr_{N,µ}(z, z′)` on a common
vertex set `Fin n`, with fixed vertices `w₁, …, w_{2µ}` for the internal central-path vertices and
fixed vertex sets `inL`, `inR` for the two sides.

B. Jauregui, M. Miyamoto, *Quantum Advantage in Local Certification of Graph Properties*,
STOC 2027 submission (manuscript sha256 b707143b…0c51), proof of Theorem 29, p.42. -/
structure Labelling (N μ n U : ℕ) where
  /-- The instance assigned to `T^tr_{N,µ}(z, z′)`. -/
  lab : (Fin N → Bool) → (Fin N → Bool) → Instance n U
  /-- The nodes `w₁, …, w_{2µ}` of the central path. -/
  w : Fin (2 * μ) → Fin n
  /-- The nodes of the left side. -/
  inL : Set (Fin n)
  /-- The nodes of the right side. -/
  inR : Set (Fin n)

/-- The identifier and port assignment of the proof of Theorem 29 (p.42): "we can keep the
identifiers of h_L, h_R and all w_j fixed. Second, within each side, enumerate the vertices other
than its root in a fixed order determined by the encoded string, and assign them the remaining
identifiers from the interval reserved for that side in increasing order. Third, choose the
internal port numbering of each side in the same way, and keep the ports along the central path,
including its attachments to h_L and h_R, fixed. Consequently, whenever the same string occurs on
the same side of two instances, that side has identical identifiers and ports."

`SideCompatible` lists the properties of that assignment used by Claim C: for balanced strings,
1. the left and right vertex sets are disjoint;
2. `lab z z′` is the tree `T^tr_{N,µ}(z, z′)`, by an isomorphism that sends `w_j` to `w j`, the
   left side (with `h_L`) into `inL` and the right side (with `h_R`) into `inR`;
3. on the left side, neighbours in port order and identifiers depend only on `z`;
4. on the right side they depend only on `z′`;
5. on the central path they depend on neither string.

**Formalization Note.** "Ports" are the neighbour lists `nbr v` in port order, so equality of
`nbr v` is equality of the port numbering of `v`, including its ports on the central path. -/
def Labelling.SideCompatible {N μ n U : ℕ} (L : Labelling N μ n U) : Prop :=
  Disjoint L.inL L.inR ∧
  (∀ z z' : Fin N → Bool, Balanced z → Balanced z' →
    ∃ φ : Ttr N μ z z' ≃g (L.lab z z').G,
      (∀ j, φ (.path j) = L.w j) ∧ (∀ x, φ (.left x) ∈ L.inL) ∧ (∀ x, φ (.right x) ∈ L.inR)) ∧
  (∀ z z₁ z₂ : Fin N → Bool, Balanced z → Balanced z₁ → Balanced z₂ → ∀ v ∈ L.inL,
    (L.lab z z₁).nbr v = (L.lab z z₂).nbr v ∧ (L.lab z z₁).id v = (L.lab z z₂).id v) ∧
  (∀ z' z₁ z₂ : Fin N → Bool, Balanced z' → Balanced z₁ → Balanced z₂ → ∀ v ∈ L.inR,
    (L.lab z₁ z').nbr v = (L.lab z₂ z').nbr v ∧ (L.lab z₁ z').id v = (L.lab z₂ z').id v) ∧
  (∀ z₁ z₁' z₂ z₂' : Fin N → Bool, Balanced z₁ → Balanced z₁' → Balanced z₂ → Balanced z₂' →
    ∀ j, (L.lab z₁ z₁').nbr (L.w j) = (L.lab z₂ z₂').nbr (L.w j) ∧
      (L.lab z₁ z₁').id (L.w j) = (L.lab z₂ z₂').id (L.w j))

end QLocalCert


