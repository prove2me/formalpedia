-- Prove2me | Definitions.Def_UnderstandingML_Compression
-- name    : UnderstandingML_Compression
-- status  : Definition
-- author  : @naimengye
-- created : 2026-09-24T05:59:44.076987+00:00
-- url     : https://prove2.me/theorems/bfb7e661-4cb1-4d13-a7f3-b6f5543b2001
-- title:
--   Chapter 30: compressed hypotheses B(S_I), the held-out set V and loss L_V, compression schemes for realizable and unrealizable sequences (Definitions 30.4–30.5), axis-aligned rectangles
-- statement:
--   Chapter 30 of Shalev-Shwartz and Ben-David. `compressedHyp B sel S` is the hypothesis $B(z_{i_1}, \dots, z_{i_k})$ built from the examples of $S$ at the indices $(i_1, \dots, i_k) = \mathrm{sel}(S) \in [m]^k$ (Theorem 30.2); `unselected sel S` is $V$, the positions of $S$ not selected, and `heldOutRisk loss sel S h` is $L_V(h)$. **Definition 30.4.** `HasCompressionScheme H k`: for every $m \ge 1$ there are $A : Z^m \to [m]^k$ and $B : Z^k \to H$ such that for every $h \in H$ and every sample $(x_1, h(x_1)), \dots, (x_m, h(x_m))$, $h' = B(S_{A(S)})$ has $L_S(h') = 0$. **Definition 30.5.** `HasAgnosticCompressionScheme H k`: the same with $L_S(h') \le L_S(h)$ for all $h \in H$ on every sample, for the multiclass 0–1 loss. `boxClass d` is the class of axis-aligned (closed) rectangles in $\mathbb{R}^d$ (§30.2.1).
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §30.1 pp. 410-412 (the protocol, Theorem 30.2's A and V, Definitions 30.4-30.5), §30.2.1 p. 412

import Definitions.Def_UnderstandingML_Linear
import Definitions.Def_UnderstandingML_MulticlassLearnability

/-!
# Shalev-Shwartz and Ben-David, *Understanding Machine Learning*, Chapter 30: compression bounds

Shalev-Shwartz and Ben-David, *Understanding Machine Learning: From Theory to Algorithms*,
Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §30.1–§30.2.

**The protocol (§30.1, pp. 410–411).** A sequence of `k` indices `I = (i₁, …, i_k) ∈ [m]^k` is
fixed, a sample `S = (z₁, …, z_m)` is drawn, `T = S_I = (z_{i₁}, …, z_{i_k})` and `V` is the rest
of the examples in `S`; a hypothesis `h_T = B(T)` is built from `T` and its loss on `V`
estimates its risk (Lemma 30.1). A learning rule `A` with `A(S) = B(z_{i₁}, …, z_{i_k})` for some
`I ∈ [m]^k` obeys the compression bound of Theorem 30.2.

**Compression schemes (Definitions 30.4–30.5, pp. 411–412).** `H` has a compression scheme of
size `k` if for all `m` there are `A : Z^m → [m]^k` and `B : Z^k → H` such that for every
`h ∈ H` and every sample labeled by `h`, `B(S_{A(S)})` has zero empirical error on `S`; in the
unrealizable version, for every sample `S`, `B(S_{A(S)})` has empirical error at most that of
every `h ∈ H`.

**Conventions.** Index sequences may repeat entries, as in `[m]^k`; the held-out set `V` is the
set of sample positions not selected, and `L_V` averages over it. Schemes are required for
every sample size `m ≥ 1` (for `m = 0` there is no index to select). Losses are the multiclass
0–1 loss of Chapter 29 for schemes and an arbitrary `[0,1]`-valued loss for the bounds.
Axis-aligned rectangles in `ℝ^d` are closed boxes `∏ᵢ [aᵢ, bᵢ]`.
-/

open MeasureTheory
open scoped InnerProductSpace

namespace UnderstandingML

section Protocol

variable {Z Hyp : Type*}

/-- The hypothesis `B(z_{i₁}, …, z_{i_k})` built from the examples of `S` selected by `sel`
(Theorem 30.2). -/
def compressedHyp {k m : ℕ} (B : (Fin k → Z) → Hyp) (sel : (Fin m → Z) → Fin k → Fin m)
    (S : Fin m → Z) : Hyp :=
  B (fun j ↦ S (sel S j))

open Classical in
/-- `V`: the positions of `S` not selected by `sel` (Theorem 30.2). -/
noncomputable def unselected {k m : ℕ} (sel : (Fin m → Z) → Fin k → Fin m) (S : Fin m → Z) :
    Finset (Fin m) :=
  Finset.univ.filter (fun i ↦ ∀ j, sel S j ≠ i)

/-- `L_V(h)`: the empirical loss of `h` on the held-out examples `V` of `S`. -/
noncomputable def heldOutRisk {k m : ℕ} (loss : Hyp → Z → ℝ) (sel : (Fin m → Z) → Fin k → Fin m)
    (S : Fin m → Z) (h : Hyp) : ℝ :=
  (∑ i ∈ unselected sel S, loss h (S i)) / (unselected sel S).card

end Protocol

section Schemes

variable {X Y : Type*}

/-- **Definition 30.4 (Compression Scheme).** `H` has a compression scheme of size `k`: for every
`m ≥ 1` there are `A : Z^m → [m]^k` and `B : Z^k → H` such that for every `h ∈ H` and every
sample `(x₁, h(x₁)), …, (x_m, h(x_m))`, the hypothesis `B(S_{A(S)})` satisfies `L_S(h') = 0`. -/
def HasCompressionScheme (H : Set (X → Y)) (k : ℕ) : Prop :=
  ∀ m : ℕ, 0 < m → ∃ (sel : (Fin m → X × Y) → Fin k → Fin m) (B : (Fin k → X × Y) → (X → Y)),
    (∀ T, B T ∈ H) ∧ ∀ h ∈ H, ∀ x : Fin m → X,
      ∀ i, compressedHyp B sel (fun i ↦ (x i, h (x i))) (x i) = h (x i)

/-- **Definition 30.5 (Compression Scheme for Unrealizable Sequences).** For every `m ≥ 1` there
are `A : Z^m → [m]^k` and `B : Z^k → H` such that for every sample `S`, `B(S_{A(S)})` satisfies
`L_S(h') ≤ L_S(h)` for all `h ∈ H`. -/
def HasAgnosticCompressionScheme (H : Set (X → Y)) (k : ℕ) : Prop :=
  ∀ m : ℕ, 0 < m → ∃ (sel : (Fin m → X × Y) → Fin k → Fin m) (B : (Fin k → X × Y) → (X → Y)),
    (∀ T, B T ∈ H) ∧ ∀ S : Fin m → X × Y, ∀ h ∈ H,
      empRisk lossMulti S (compressedHyp B sel S) ≤ empRisk lossMulti S h

end Schemes

section Boxes

open Classical in
/-- The class of **axis-aligned rectangles** (closed boxes) in `ℝ^d` (§30.2.1). -/
noncomputable def boxClass (d : ℕ) : Set ((Fin d → ℝ) → Bool) :=
  {h | ∃ a b : Fin d → ℝ, h = fun x ↦ decide (∀ i, a i ≤ x i ∧ x i ≤ b i)}

end Boxes

end UnderstandingML


