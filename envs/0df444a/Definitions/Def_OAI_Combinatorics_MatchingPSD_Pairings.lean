-- Prove2me | Definitions.Def_OAI_Combinatorics_MatchingPSD_Pairings
-- name    : OAI_Combinatorics_MatchingPSD_Pairings
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T03:24:52.341984+00:00
-- url     : https://prove2.me/theorems/f7d2ccd4-f17c-4753-a59b-97df3d905623
-- title:
--   Perfect matchings as fixed-point-free involutions: relabelling action, restriction and edge coordinates
-- statement:
--   Throughout, $V$ is an arbitrary set of vertices. A **pairing** (perfect matching) of $V$ is a permutation $M$ of $V$ that is an involution without fixed points:
--
--   $$
--   M(M(a)) = a \quad\text{and}\quad M(a) \neq a \qquad \text{for all } a \in V .
--   $$
--
--   The vertex $M(a)$ is the partner of $a$, and the edges of the matching are the two-element sets $\{a, M(a)\}$. Write $\mathcal{M}(V)$ for the set of pairings of $V$. The module defines the following structure.
--
--   1. **Relabelling.** For a permutation $p$ of $V$, the relabelled pairing is the conjugate $p \cdot M = p M p^{-1}$, so $(p \cdot M)(a) = p\bigl(M(p^{-1}(a))\bigr)$; its edges are the images $\{p(a), p(M(a))\}$ of the edges of $M$. This is a left action of the symmetric group: $1 \cdot M = M$ and $(pq) \cdot M = p \cdot (q \cdot M)$. For fixed $p$, the map $M \mapsto p \cdot M$ is a bijection of $\mathcal{M}(V)$ with inverse $M \mapsto p^{-1} \cdot M$.
--   2. **Action on functions.** For a permutation $p$, the linear automorphism $T_p$ of the space $\mathbb{R}^{\mathcal{M}(V)}$ of real functions on pairings is $(T_p f)(M) = f(p^{-1} \cdot M)$. It satisfies $T_{pq} = T_p T_q$ and $T_1 = \mathrm{id}$, so it is the permutation representation of the symmetric group on functions of matchings.
--   3. **Same internal structure.** For a finite set $U \subseteq V$, two pairings $M, N$ have the same internal structure on $U$ if $M(a) = b \iff N(a) = b$ for all $a, b \in U$, i.e. they contain exactly the same edges with both endpoints in $U$.
--   4. **Restriction.** If a finite set $S \subseteq V$ is closed under $M$, in the sense that $M(a) \in S \iff a \in S$ for every $a \in V$, then $M$ restricts to a pairing of $S$ with the same partner map.
--   5. **Closure.** For a finite set $U \subseteq V$, the closure $U \cup M(U)$ adds to $U$ the partners of its elements; it is the smallest $M$-closed set containing $U$.
--   6. **Edge coordinates.** For an ordered pair $e = (a, b)$ of vertices, the edge coordinate is the indicator function $x_e : \mathcal{M}(V) \to \mathbb{R}$ with $x_e(M) = 1$ if $M(a) = b$ and $x_e(M) = 0$ otherwise. Since $M(a) = b \iff M(b) = a$, one has $x_{(a,b)} = x_{(b,a)}$, and $x_{(a,a)} = 0$.
--   7. **Internal pattern.** For a finite set $U \subseteq V$, the internal pattern of $M$ on $U$ is the set of ordered pairs $(a, b) \in U \times U$ with $M(a) = b$, i.e. the edges of $M$ inside $U$ listed in both orientations. Two pairings have the same internal pattern on $U$ exactly when they have the same internal structure on $U$.
--
--   These are the basic objects for analysing real functions on perfect matchings: low-degree polynomials are formed from the edge coordinates, symmetry arguments use the relabelling action, and the internal pattern on a finite set $U$ is the device showing that a function on matchings of a finite vertex set which is invariant under every transposition of two vertices outside $U$ is a polynomial of degree at most $|U|^2$ in the edge coordinates.
--
--   **Formalization Note** `Pairing α` is the subtype of `Equiv.Perm α` consisting of involutions without fixed points; `relabel`, `relabelEquiv`, `act`, `SameInternal`, `restrict`, `closure`, `edgeCoord` and `internalPattern` are items 1 to 7. The module also records the elementary facts `ext`, `partner_partner` ($M(M(a)) = a$), `partner_ne`, `partner_eq_iff` ($M(a) = b \iff M(b) = a$), `partner_sq` ($M^2 = 1$), `relabel_apply`, `relabel_one`, `relabel_mul`, `act_apply`, `act_mul`, `act_one`, `restrict_apply`, and `relabel_swap_partner` (conjugating $M$ by the transposition of $a$ and $M(a)$ returns $M$). `restrict` takes the closure hypothesis as an explicit argument, and `closure`, `internalPattern` and `relabel_swap_partner` use decidable equality on the vertex type.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/MatchingPSD/Pairings.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/MatchingPSD/Pairings.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the MatchingPSD mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_MatchingPSD
import Definitions.Def_OAI_Combinatorics_MatchingPSD_EdgeProducts

namespace OAI

universe u_1 u_2

namespace MatchingSmoothing
abbrev Pairing (α : Type u_1) :=
  {M : Equiv.Perm α // Function.Involutive M ∧ ∀ a, M a ≠ a}

namespace Pairing
variable {α : Type u_2}

@[ext] lemma ext {M N : Pairing α} (h : ∀ a, M.1 a = N.1 a) : M = N :=
  Subtype.ext (Equiv.ext h)

@[simp] lemma partner_partner (M : Pairing α) (a : α) : M.1 (M.1 a) = a := M.2.1 a

lemma partner_ne (M : Pairing α) (a : α) : M.1 a ≠ a := M.2.2 a

@[simp] lemma partner_eq_iff (M : Pairing α) (a b : α) : M.1 a = b ↔ M.1 b = a := by
  constructor <;> intro h <;> rw [← h, partner_partner]

def relabel (p : Equiv.Perm α) (M : Pairing α) : Pairing α :=
  ⟨p * M.1 * p⁻¹, by
    constructor
    · intro a
      simp [Equiv.Perm.mul_apply]
    · intro a h
      apply M.partner_ne (p⁻¹ a)
      simpa using
        congrArg (fun b => p⁻¹ b) h⟩

@[simp] lemma relabel_apply (p : Equiv.Perm α) (M : Pairing α) (a : α) :
    (relabel p M).1 a = p (M.1 (p⁻¹ a)) := rfl

@[simp] lemma relabel_one (M : Pairing α) : relabel 1 M = M := by ext a; simp

@[simp] lemma relabel_mul (p q : Equiv.Perm α) (M : Pairing α) :
    relabel (p * q) M = relabel p (relabel q M) := by
  ext a
  simp [Equiv.Perm.mul_apply]

def relabelEquiv (p : Equiv.Perm α) : Equiv.Perm (Pairing α) where
  toFun := relabel p
  invFun := relabel p⁻¹
  left_inv M := by rw [← relabel_mul, inv_mul_cancel, relabel_one]
  right_inv M := by rw [← relabel_mul, mul_inv_cancel, relabel_one]

def act (p : Equiv.Perm α) : (Pairing α → ℝ) ≃ₗ[ℝ] (Pairing α → ℝ) where
  toFun f M := f (relabel p⁻¹ M)
  invFun f M := f (relabel p M)
  left_inv f := by ext M; simp [← relabel_mul]
  right_inv f := by ext M; simp [← relabel_mul]
  map_add' f g := rfl
  map_smul' c f := rfl

@[simp] lemma act_apply (p : Equiv.Perm α) (f : Pairing α → ℝ) (M : Pairing α) :
    act p f M = f (relabel p⁻¹ M) := rfl

@[simp] lemma act_mul (p q : Equiv.Perm α) (f : Pairing α → ℝ) :
    act (p * q) f = act p (act q f) := by
  ext M
  simp [← relabel_mul]

@[simp] lemma act_one (f : Pairing α → ℝ) : act 1 f = f := by ext M; simp

@[simp] lemma partner_sq (M : Pairing α) : M.1 ^ 2 = 1 := by
  ext a
  simp [pow_two, Equiv.Perm.mul_apply]

@[simp] lemma relabel_swap_partner [DecidableEq α] (M : Pairing α) (a : α) :
    relabel (Equiv.swap a (M.1 a)) M = M := by
  apply Subtype.ext
  change Equiv.swap a (M.1 a) * M.1 * (Equiv.swap a (M.1 a))⁻¹ = M.1
  have hc : M.1 * Equiv.swap a (M.1 a) = Equiv.swap a (M.1 a) * M.1 := by
    rw [Equiv.mul_swap_eq_swap_mul, partner_partner, Equiv.swap_comm]
  rw [← hc, mul_inv_cancel_right]

def SameInternal (U : Finset α) (M N : Pairing α) : Prop :=
  ∀ a ∈ U, ∀ b ∈ U, M.1 a = b ↔ N.1 a = b

def restrict (M : Pairing α) (S : Finset α)
    (hS : ∀ a, M.1 a ∈ S ↔ a ∈ S) : Pairing S :=
  ⟨M.1.subtypePerm hS, by
    constructor
    · intro a; apply Subtype.ext; exact M.partner_partner a.1
    · intro a h; exact M.partner_ne a.1 (congrArg Subtype.val h)⟩

@[simp] lemma restrict_apply (M : Pairing α) (S : Finset α)
    (hS : ∀ a, M.1 a ∈ S ↔ a ∈ S) (a : S) :
    ((restrict M S hS).1 a).1 = M.1 a.1 := rfl

def closure [DecidableEq α] (M : Pairing α) (U : Finset α) : Finset α :=
  U ∪ U.image M.1

noncomputable def edgeCoord (e : α × α) (M : Pairing α) : ℝ := by
  classical
  exact if M.1 e.1 = e.2 then 1 else 0

noncomputable def internalPattern [DecidableEq α] (U : Finset α)
    (M : Pairing α) : Finset (α × α) :=
  (U ×ˢ U).filter fun e => M.1 e.1 = e.2

end Pairing
end MatchingSmoothing

end OAI


