-- Prove2me | Definitions.Def_LiftSAParity_Supplement_tClosure
-- name    : LiftSAParity_Supplement_tClosure
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T14:13:30.782832+00:00
-- url     : https://prove2.me/theorems/984a3190-8f61-4b0d-8d0d-ac085dbcbf00
-- title:
--   $t$-safe affine spaces and the $t$-closure $\mathrm{Cl}^t(A)$
-- statement:
--   Work in $\mathbb F_2^{[n]\times[\ell]}$, with $n$ blocks of $\ell$ variables. A linear form $f=\sum_{v\in S}x_v$ has variables $\mathrm{Vars}(f)=S$; for a set of blocks $B\subseteq[n]$, $f[\setminus B]$ deletes the variables of the blocks in $B$.
--
--   1. A nonempty affine space $A$ is **$t$-safe** if every nonzero linear form that is constant on $A$ has more than $t$ variables.
--   2. $A$ is **$t$-safe outside** $B\subseteq[n]$ if every linear form $f$ constant on $A$ satisfies $f[\setminus B]=0$ or $|\mathrm{Vars}(f[\setminus B])|>t$.
--   3. The **$t$-closure** $\mathrm{Cl}^t(A)$ of a nonempty affine space $A$ is the unique inclusion-minimal set of blocks outside which $A$ is $t$-safe (it exists by Lemma 5.1).
--   4. $\mathrm{Vars}(A)\subseteq W$ means that $A$ has a defining system $\{f_1(x)=b_1,\dots,f_k(x)=b_k\}$ whose linear forms use only variables of $W$.
--
--   The closure collects the blocks on which $A$ is overly constrained; Section 5 samples from the local distribution on $\mathrm{Cl}^t(A)$ and uniformly elsewhere.
--
--   **Formalization Note** A linear form is its support `S : Finset`; "nonzero" is `S.Nonempty`. `tClosure t A` is defined as the intersection of all sets of blocks outside which $A$ is $t$-safe. For a nonempty affine space this is the paper's minimal set: the proof of Lemma 5.1 builds a set contained in every such set, outside which $A$ is $t$-safe. `IsTSafe` includes nonemptiness, as the paper's definition does.
-- source:
--   de Rezende, Engström, Shekhovtsov, Lifting Sherali-Adams Degree to Unary Sherali-Adams over Parities Size (manuscript, sha256 cab5a032…), §2, p.7 (eq. (2), eq. (3)); §5.1, p.17 (t-safe, Lemma 5.1, t-closure); Definition 5.3, p.18 (Vars(A))

import Mathlib
import Definitions.Def_LiftSAParity_IsAffineSpace

namespace LiftSAParity

namespace Supplement

open Classical

/-- `A` is **t-safe** (de Rezende–Engström–Shekhovtsov, *Lifting Sherali-Adams Degree to Unary
Sherali-Adams over Parities Size*, manuscript (sha256 cab5a032…), §5.1, p.17): "Let A be a
nonempty affine space. We say that A is t-safe if every nonzero linear form that is constant on A
has more than t variables."

**Formalization Note** A linear form is given by its support `S` (`f_S = ∑_{v∈S} x_v`); it is
nonzero iff `S` is nonempty, and `|Vars(f_S)| = |S|`. Nonemptiness of `A` is part of the
definition, as in the paper. -/
def IsTSafe {n ℓ : ℕ} (t : ℕ) (A : Set (Fin n × Fin ℓ → ZMod 2)) : Prop :=
  A.Nonempty ∧ ∀ S : Finset (Fin n × Fin ℓ), S.Nonempty → IsConstOn S A → t < S.card

/-- `A` is **t-safe outside** the set of blocks `B ⊆ [n]` (§5.1, p.17): "every linear form f that
is constant on A satisfies either f[\S] = 0 or |Vars(f[\S])| > t", where `f[\B]` deletes the
variables of the blocks in `B` (§2, p.7, eq. (2)); on supports, `supp(f_S[\B]) = {v ∈ S : v.1 ∉ B}`. -/
def IsTSafeOutside {n ℓ : ℕ} (t : ℕ) (A : Set (Fin n × Fin ℓ → ZMod 2)) (B : Finset (Fin n)) :
    Prop :=
  ∀ S : Finset (Fin n × Fin ℓ), IsConstOn S A →
    S.filter (fun v => v.1 ∉ B) = ∅ ∨ t < (S.filter (fun v => v.1 ∉ B)).card

/-- The **t-closure** `Cl^t(A)` (§5.1, p.17): "the unique inclusion-minimal set of blocks outside
which A is t-safe" (it exists by Lemma 5.1).

**Formalization Note** Defined as the intersection of all sets of blocks outside which `A` is
t-safe (`[n]` is always one). For a nonempty affine space `A` this is the paper's `Cl^t(A)`: the
proof of Lemma 5.1 constructs a set `S` contained in every such set `T`, and `A` is t-safe outside
`S`, so the intersection equals `S`. Only used for nonempty affine `A`. -/
noncomputable def tClosure {n ℓ : ℕ} (t : ℕ) (A : Set (Fin n × Fin ℓ → ZMod 2)) :
    Finset (Fin n) :=
  Finset.univ.filter (fun i => ∀ B : Finset (Fin n), IsTSafeOutside t A B → i ∈ B)

/-- `Vars(A) ⊆ W` (§5.2, p.18, Definition 5.3 (1)): `A` has a defining system
`{f₁(x) = b₁, …, f_k(x) = b_k}` (§2, p.7, eq. (3)) all of whose linear forms use only variables
in `W`. -/
def DefinedOn {V : Type*} (A : Set (V → ZMod 2)) (W : Finset V) : Prop :=
  ∃ (k : ℕ) (S : Fin k → Finset V) (b : Fin k → ZMod 2),
    (∀ s, S s ⊆ W) ∧ A = {y | ∀ s, parity (S s) y = b s}

end Supplement

end LiftSAParity


