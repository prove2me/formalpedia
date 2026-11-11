-- Prove2me | Definitions.Def_ExactAutobid_Equilibria_FIXPa
-- name    : ExactAutobid_Equilibria_FIXPa
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T21:56:07.83221+00:00
-- url     : https://prove2.me/theorems/61a8810d-d58f-40dc-af61-453d5e31c70b
-- title:
--   Discrete search problems, polynomial-time search reductions, strong approximation and FIXPa (§2.2)
-- statement:
--   A **discrete search problem** $\Pi$ consists of instances $I$ with an injective binary encoding $\langle I\rangle$ over the alphabet $\mathrm{Sym}$ and, for each instance, a set $\mathrm{Ans}_\Pi(I)$ of admissible answers, each a finite vector of rationals.
--
--   A **polynomial-time search reduction** from $P$ to $Q$ is a pair of polynomial-time maps, an instance map $f$ and an answer map $g$, such that
--   $$z \in \mathrm{Ans}_Q(f(I)) \;\Longrightarrow\; g(I, z) \in \mathrm{Ans}_P(I).$$
--
--   The **strong approximation** (approximation in distance) of a real search problem $\Pi$ with respect to its first $k(I)$ coordinates has instances $(I, \varepsilon)$ with $\varepsilon \in \mathbb{Q}_{>0}$, and its answers are the rational vectors $z$ of length $k(I)$ with $\max_{i<k(I)} |z_i - y_i| \le \varepsilon$ for **some** exact solution $y \in \mathrm{Sol}_\Pi(I)$. The class **FIXPa** [Etessami–Yannakakis 2010] consists of the discrete search problems that reduce in polynomial time to the strong approximation of basic FIXP; FIXPa-hardness and FIXPa-completeness are defined as usual.
--
--   These are the notions of §2.2 behind the "approximation in distance" clauses of Theorems 4.1, 5.1, 6.1 and 7.1: for the auction problems only the control vector (multipliers or participation probabilities) is approximated.
--
--   **Formalization Note.** Polynomial time is Mathlib's `Turing.TM2ComputableInPolyTime`, as in the reused FIXP framework; answers are encoded as framed lists of binary rationals, and the pair $(I, \varepsilon)$ as the framed encoding of $I$ followed by $\varepsilon$.
-- source:
--   Huang, Liu, Yan, On the Complexity of Exact Autobidding Equilibria, arXiv:2611.04475 (sha256 270d1b74…), §2.2, p. 5 (FIXPa and strong approximation; [EY10])

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_FixpReciprocal_frame
import Definitions.Def_FixpReciprocal_RealSearch
import Definitions.Def_FixpReciprocal_basicFIXP

namespace ExactAutobid.Equilibria

open OnlineCRS.Combine FixpReciprocal

/-- **A discrete search problem**: instances with an injective binary encoding over `Sym`, and for
each instance a set of admissible answers, each answer a finite vector of rationals.

Huang, Liu, Yan, *On the Complexity of Exact Autobidding Equilibria*, arXiv:2611.04475
(sha256 270d1b74…), §2.2, p. 5: FIXPa is a class of discrete search problems [EY10]. -/
structure DiscreteSearch where
  /-- the instances -/
  Inst : Type
  /-- the encoding of an instance -/
  enc : Inst → List Sym
  /-- distinct instances have distinct encodings -/
  enc_injective : Function.Injective enc
  /-- the admissible answers of an instance -/
  Ans : Inst → Set (List ℚ)

/-- **Polynomial-time search reduction** `P ≤ Q` [EY10]: a polynomial-time instance map `f` and a
polynomial-time answer map `g` such that every answer `z` of `f(I)` is mapped to an answer
`g(I, z)` of `I`. Answers are encoded as framed lists of binary rationals (`fList fRat`); the
answer map reads the framed instance followed by the answer. -/
def SearchReduces (P Q : DiscreteSearch) : Prop :=
  ∃ (f : P.Inst → Q.Inst) (g : P.Inst × List ℚ → List ℚ),
    Nonempty (Turing.TM2ComputableInPolyTime P.enc Q.enc f) ∧
    Nonempty (Turing.TM2ComputableInPolyTime
      (fun p : P.Inst × List ℚ => frame (P.enc p.1) ++ fList fRat p.2) (fList fRat) g) ∧
    ∀ (I : P.Inst) (z : List ℚ), z ∈ Q.Ans (f I) → g (I, z) ∈ P.Ans I

theorem frame_append_fRat_injective {α : Type} {e : α → List Sym} (he : Function.Injective e) :
    Function.Injective (fun p : α × {ε : ℚ // 0 < ε} => frame (e p.1) ++ fRat p.2.1) := by
  rintro ⟨a, ε⟩ ⟨b, δ⟩ h
  obtain ⟨h1, h2⟩ := frame_append_inj h
  have h3 := fRat_prefixFree.injective h2
  simp only [Prod.mk.injEq]
  exact ⟨he h1, Subtype.ext h3⟩

/-- **Strong approximation (approximation in distance)** of a real search problem `Π`, for the
first `k(I)` coordinates of a solution: an instance is a pair `(I, ε)` of an instance of `Π` and a
rational `ε > 0`; an answer is a rational vector `z` of length `k(I)` within `ε` in `ℓ∞` of the
first `k(I)` coordinates of **some** exact solution `y ∈ Sol_Π(I)`.

Huang, Liu, Yan, arXiv:2611.04475 (sha256 270d1b74…), §2.2, p. 5: "This task asks for a rational
vector within a supplied rational ε > 0 of some exact solution in the maximum norm … our
approximation concerns only the multiplier or participation vector."

**Formalization Note.** `k` selects the control coordinates (the multipliers or participation
probabilities, listed first in every solution vector of this mission); `k = dim` approximates the
whole solution. The pair is encoded as the framed encoding of `I` followed by `ε` in binary. -/
def StrongApprox (P : RealSearch) (k : P.Inst → ℕ) : DiscreteSearch where
  Inst := P.Inst × {ε : ℚ // 0 < ε}
  enc := fun p => frame (P.enc p.1) ++ fRat p.2.1
  enc_injective := frame_append_fRat_injective P.enc_injective
  Ans := fun p => {z | z.length = k p.1 ∧ ∃ y ∈ P.Sol p.1,
    ∀ i : ℕ, i < k p.1 → |((z.getD i 0 : ℚ) : ℝ) - lookup y i| ≤ (p.2.1 : ℝ)}

/-- **The class FIXPa** [EY10]: discrete search problems that reduce in polynomial time to the
strong approximation of basic FIXP (approximating a whole fixed point).

Huang, Liu, Yan, arXiv:2611.04475 (sha256 270d1b74…), §2.2, p. 5. -/
def InFIXPa (D : DiscreteSearch) : Prop :=
  SearchReduces D (StrongApprox basicFIXP basicFIXP.dim)

/-- **FIXPa-hardness**: every problem of FIXPa reduces in polynomial time to `Q`. -/
def FIXPaHard (Q : DiscreteSearch) : Prop :=
  ∀ D : DiscreteSearch, InFIXPa D → SearchReduces D Q

/-- **FIXPa-completeness**: membership in FIXPa and FIXPa-hardness. -/
def FIXPaComplete (Q : DiscreteSearch) : Prop := InFIXPa Q ∧ FIXPaHard Q

end ExactAutobid.Equilibria


