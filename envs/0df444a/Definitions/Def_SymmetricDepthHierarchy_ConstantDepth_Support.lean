-- Prove2me | Definitions.Def_SymmetricDepthHierarchy_ConstantDepth_Support
-- name    : SymmetricDepthHierarchy_ConstantDepth_Support
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T04:31:46.873298+00:00
-- url     : https://prove2.me/theorems/00394ddf-9f23-4c57-8c7a-d5ccd2b827fa
-- title:
--   Supports, minimal supports, support size and support depth of rigid circuits; $\kappa_f(n)$
-- statement:
--   Let $C$ be a rigid matrix-symmetric circuit over $X_n$. The group $\Gamma_n$ acts on $[n]\uplus[n]$. A set $S\subseteq[n]\uplus[n]$ **supports** a gate $g$ if the pointwise stabiliser of $S$ fixes $g$; $S_L$ and $S_R$ are its two sides. A support is **small** if $|S_L|,|S_R|<n/2$. The **minimal support** $\sup(g)$ is the intersection of all small supports of $g$; when $g$ has a small support it is the unique minimal small support and it is contained in every small support [DPS26a, Lemmas 2.1, 2.2].
--
--   1. The **support size** $\operatorname{maxSup}(C)$ is the least $k$ such that every gate of $C$ has a support of size $\le k$.
--   2. A wire from $h$ to $g$ is **support-changing** if $\sup(h)\not\subseteq\sup(g)$.
--   3. If $\operatorname{maxSup}(C)<n/2$, the **support depth** of $C$ is the maximum number of support-changing wires on a path from the output gate to an input gate; if $\operatorname{maxSup}(C)\ge n/2$ it is the depth of $C$.
--
--   For $f:\mathbb N\to\mathbb N$, equation (2) defines
--   $$\kappa_f(n)=\min\Bigl\{r\in\mathbb N:\binom{n}{r}>f(n)\Bigr\}.$$
--
--   Support size and support depth are the measures in which the paper's characterisation (Theorem 3.5) is exact.
--
--   **Formalization Note.** $[n]\uplus[n]$ is `Fin n ⊕ Fin n`. "The pointwise stabiliser fixes $g$" is stated as: every automorphism extending an element of the pointwise stabiliser fixes $g$, which is the same for rigid circuits. The source states that $\sup(g)$ is "contained in every support of $g$"; that is false for large supports (at $n=20$, in the reduced circuit summing all $400$ variables both $\{L1,R1\}$ and $\{L2,\dots,L20,R1\}$ support $x_{1,1}$), so containment is required only among small supports, and $\sup(g)$ is defined as their intersection. When $g$ has no small support the intersection is the whole set; support depth uses $\sup$ only when $\operatorname{maxSup}(C)<n/2$, where every gate has a small support. $\kappa_f(n)$ is an extended natural number, $\infty$ when no $r$ qualifies (e.g. $f(n)=2^n$). A path with no input gate at its end does not count; if there is none the maximum is $0$.
-- source:
--   Anuj Dawar, Prateek Dwivedi, Benedikt Pago, Tim Seppelt, STOC 2027 submission #1521 (October 2026), §2.3, p. 8 (PDF p. 11), and equation (2)

import Mathlib
import Definitions.Def_SymmetricDepthHierarchy_ConstantDepth_Circuit

open scoped Classical

noncomputable section

namespace SymmetricDepthHierarchy.ConstantDepth

/-!
# Supports, support size and support depth of rigid circuits; the quantity `κ_f(n)`

STOC 2027 submission #1521, §2.3 (printed p. 8, PDF p. 11) and equation (2).

`Γ_n` acts on `[n] ⊎ [n]`, encoded as `Fin n ⊕ Fin n` (left copy `inl`, right copy `inr`).
A set `S` supports a gate `g` if every automorphism extending an element of the pointwise
stabiliser of `S` fixes `g`; for a rigid circuit (the only case in which the source uses supports)
this is "the pointwise stabiliser `Stab•(S)` fixes `g`".

**Minimal supports (corrected convention).** The source says that a gate with a support `S` with
`|S_L|, |S_R| < n/2` has a unique minimal support `sup(g)` "contained in every support of `g`".
Containment in *every* support is false for large supports (at `n = 20`, the reduced circuit summing
all `400` variables: `{L1, R1}` and `{L2,…,L20, R1}` both support `x_{1,1}`). Here `sup(g)` is the
intersection of all supports that are *small* (fewer than `n/2` points on each side); by
[DPS26a, Lemmas 2.1, 2.2] this is the unique minimal small support whenever a small support exists,
and it is contained in every small support.
-/

namespace Circuit

variable {K : Type} [Field K] {n : ℕ} {V : Type} [Fintype V]

/-- `γ = (σ, τ)` fixes every point of `S ⊆ [n] ⊎ [n]`. -/
def FixesPointwise (γ : Gamma n) (S : Finset (Fin n ⊕ Fin n)) : Prop :=
  (∀ i, Sum.inl i ∈ S → γ.1 i = i) ∧ (∀ j, Sum.inr j ∈ S → γ.2 j = j)

/-- The left side `S_L` of `S ⊆ [n] ⊎ [n]`. -/
def leftPart (S : Finset (Fin n ⊕ Fin n)) : Finset (Fin n) :=
  Finset.univ.filter fun i => Sum.inl i ∈ S

/-- The right side `S_R` of `S ⊆ [n] ⊎ [n]`. -/
def rightPart (S : Finset (Fin n ⊕ Fin n)) : Finset (Fin n) :=
  Finset.univ.filter fun j => Sum.inr j ∈ S

/-- `S` supports `g`: the pointwise stabiliser of `S` fixes `g`. -/
def Supports (C : Circuit K n V) (g : V) (S : Finset (Fin n ⊕ Fin n)) : Prop :=
  ∀ (γ : Gamma n) (σ : Equiv.Perm V), FixesPointwise γ S → C.IsExtension γ σ → σ g = g

/-- A small support: a support with `|S_L| < n/2` and `|S_R| < n/2`. -/
def IsSmallSupport (C : Circuit K n V) (g : V) (S : Finset (Fin n ⊕ Fin n)) : Prop :=
  C.Supports g S ∧ 2 * (leftPart S).card < n ∧ 2 * (rightPart S).card < n

/-- The minimal support `sup(g)`: the intersection of all small supports of `g` (see the module
docstring for the corrected containment convention). -/
def minSup (C : Circuit K n V) (g : V) : Finset (Fin n ⊕ Fin n) :=
  Finset.univ.filter fun x => ∀ S, C.IsSmallSupport g S → x ∈ S

/-- The support size `maxSup(C)`: the least `k` such that every gate of `C` has a support of
size `≤ k`. (For a rigid circuit `[n] ⊎ [n]` supports every gate, so the set is nonempty.) -/
def maxSup (C : Circuit K n V) : ℕ :=
  sInf {k : ℕ | ∀ g, ∃ S : Finset (Fin n ⊕ Fin n), C.Supports g S ∧ S.card ≤ k}

/-- The wire from `h` into `g` is support-changing: `sup(h) ⊄ sup(g)`. -/
def SupportChanging (C : Circuit K n V) (h g : V) : Prop := ¬ C.minSup h ⊆ C.minSup g

/-- `k` rounds of the recursion for the maximal number of support-changing wires on a path from
an input gate up to `g` (`⊥` if no input gate lies below `g`). -/
def supportChangesAux (C : Circuit K n V) : ℕ → V → WithBot ℕ
  | 0 => fun g => if C.IsInput g then 0 else ⊥
  | k + 1 => fun g => if C.IsInput g then 0 else
      Finset.univ.sup fun h =>
        if C.Wire h g then C.supportChangesAux k h + (if C.SupportChanging h g then 1 else 0)
        else ⊥

/-- The support depth of a rigid circuit `C` (§2.3): if `maxSup(C) < n/2`, the maximum number of
support-changing wires on a path from the output gate to an input gate (`0` if there is no such
path); if `maxSup(C) ≥ n/2`, the depth of `C`. -/
def rigidSupportDepth (C : Circuit K n V) : ℕ :=
  if 2 * C.maxSup < n then (C.supportChangesAux (Fintype.card V) C.out).unbotD 0 else C.depth

end Circuit

/-- Equation (2): `κ_f(n) = min {r ∈ ℕ : binom(n, r) > f(n)}`, as an extended natural number,
equal to `⊤` when no such `r` exists (e.g. `f(n) = 2^n`). -/
def kappa (f : ℕ → ℕ) (n : ℕ) : ℕ∞ :=
  sInf ((fun r : ℕ => (r : ℕ∞)) '' {r : ℕ | f n < n.choose r})

end SymmetricDepthHierarchy.ConstantDepth


