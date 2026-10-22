-- Prove2me | Definitions.Def_MWT_tor
-- name    : MWT_tor
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-22T02:09:38.401313+00:00
-- url     : https://prove2.me/theorems/ec99778b-29e3-46fa-bdef-91b6dc90ddae
-- title:
--   The world layer: the idealized multi-welded twin group and the universal welded epimorphism
-- statement:
--   The idealized multi-welded twin group of Definition 2.1: the group with the twin generators s_i and the k virtual families of generators rho_i^(alpha), subject to the relations (2.1) through (2.9) - the involutivity of the twin generators with their distant commutation, the involutivity of the virtual generators with their braid and distant relations, the mixed commutation, the MR2-type relations, the commutation of distinct virtual families, the two virtual mixed relations, and the welded relations. The world extends the structure with the permutation epimorphism onto the symmetric group, carrying each generator to the corresponding transposition, and with the canonical epimorphism from the universal welded group UW_n(k), given by its values on the generators: the virtual generators map to the distinguished virtual family, the first k-1 non-virtual families map to the remaining virtual families, and the last non-virtual family maps to the twin generators, as in Proposition 2.3.
-- source:
--   M. N. Nasser, O. Ocampo, Multi-welded twin groups, arXiv:2605.31298 (2026), Section 2 (Definition 2.1, Remark 2.2, and Proposition 2.3).

import Mathlib
import Definitions.Def_MWT_alg

/-!
# The world layer: the idealized multi-welded twin group

The world layer of the MWT mission: the idealized multi-welded twin group
M_kWT_n of Definition 2.1 of the source paper of Mohamad N. Nasser and
Oscar Ocampo - the group with the twin generators s_i and the k virtual
families rho_i^(alpha) subject to the relations (2.1) through (2.9) -
together with the permutation epimorphism onto the symmetric group and the
canonical epimorphism from the idealized universal welded group UW_n(k)
identifying the virtual generators with the distinguished virtual family,
the first k-1 non-virtual families with the remaining virtual families,
and the last non-virtual family with the twin generators, as in
Proposition 2.3.
-/

namespace MWT

/-- The multi-welded twin structure of Definition 2.1: the group G with the
twin generators s and the k virtual families rho, satisfying the twin and
virtual Coxeter relations (2.1) through (2.3), the mixed commutation (2.4),
the MR2-type relations (2.5), the virtual commutation (2.6), the virtual
mixed relations (2.7) and (2.8), and the welded relations (2.9). -/
structure MultiWeldedTwinStructure (n k : ℕ) (G : Type*) [Group G] where
  s : Fin (n - 1) → G
  rho : Fin k → Fin (n - 1) → G
  s_sq : ∀ i : Fin (n - 1), s i * s i = 1
  s_comm : ∀ i j : Fin (n - 1), i.val + 2 ≤ j.val ∨ j.val + 2 ≤ i.val →
    s i * s j = s j * s i
  rho_sq : ∀ (α : Fin k) (i : Fin (n - 1)), rho α i * rho α i = 1
  rho_braid : ∀ (α : Fin k) (i : ℕ) (hi : i + 3 ≤ n),
    rho α ⟨i, by omega⟩ * rho α ⟨i + 1, by omega⟩ * rho α ⟨i, by omega⟩
      = rho α ⟨i + 1, by omega⟩ * rho α ⟨i, by omega⟩ * rho α ⟨i + 1, by omega⟩
  rho_comm : ∀ (α : Fin k) (i j : Fin (n - 1)), i.val + 2 ≤ j.val ∨ j.val + 2 ≤ i.val →
    rho α i * rho α j = rho α j * rho α i
  mixed_comm : ∀ (α : Fin k) (i j : Fin (n - 1)), i.val + 2 ≤ j.val ∨ j.val + 2 ≤ i.val →
    rho α i * s j = s j * rho α i
  mr2 : ∀ (α : Fin k) (i : ℕ) (hi : i + 3 ≤ n),
    rho α ⟨i, by omega⟩ * rho α ⟨i + 1, by omega⟩ * s ⟨i, by omega⟩
      = s ⟨i + 1, by omega⟩ * rho α ⟨i, by omega⟩ * rho α ⟨i + 1, by omega⟩
  vcomm : ∀ (α β : Fin k) (i j : Fin (n - 1)),
    (i.val + 2 ≤ j.val ∨ j.val + 2 ≤ i.val) → α ≠ β →
    rho α i * rho β j = rho β j * rho α i
  vmixed1 : ∀ (α β : Fin k), (α : ℕ) < (β : ℕ) → ∀ (i : ℕ) (hi : i + 3 ≤ n),
    rho α ⟨i, by omega⟩ * rho β ⟨i + 1, by omega⟩ * rho β ⟨i, by omega⟩
      = rho β ⟨i + 1, by omega⟩ * rho β ⟨i, by omega⟩ * rho α ⟨i + 1, by omega⟩
  vmixed2 : ∀ (α β : Fin k), (α : ℕ) < (β : ℕ) → ∀ (i : ℕ) (hi : i + 3 ≤ n),
    rho α ⟨i, by omega⟩ * rho α ⟨i + 1, by omega⟩ * rho β ⟨i, by omega⟩
      = rho β ⟨i + 1, by omega⟩ * rho α ⟨i, by omega⟩ * rho α ⟨i + 1, by omega⟩
  welded : ∀ (α : Fin k) (i : ℕ) (hi : i + 3 ≤ n),
    rho α ⟨i, by omega⟩ * s ⟨i + 1, by omega⟩ * s ⟨i, by omega⟩
      = s ⟨i + 1, by omega⟩ * s ⟨i, by omega⟩ * rho α ⟨i + 1, by omega⟩

/-- The idealized world of the multi-welded twin group: the structure of
Definition 2.1 together with the epimorphism onto the symmetric group
carrying each generator to the corresponding transposition, and the
canonical epimorphism from the idealized universal welded group UW_n(k)
given by its values on the generators, as in Proposition 2.3. -/
structure MultiWeldedTwinWorld (n k : ℕ) (G UW : Type*) [Group G] [Group UW]
    extends MultiWeldedTwinStructure n k G where
  hk : 0 < k
  perm : G →* Equiv.Perm (Fin n)
  uwRho : Fin (n - 1) → UW
  uwSigma : Fin (n - 1) → Fin k → UW
  uw : UW →* G
  uwRhoMap : ∀ i : Fin (n - 1), uw (uwRho i) = rho ⟨0, by omega⟩ i
  uwSigmaMap : ∀ (i : Fin (n - 1)) (t : Fin k),
    uw (uwSigma i t) = if h : (t : ℕ) + 1 < k then rho ⟨(t : ℕ) + 1, h⟩ i else s i

end MWT


