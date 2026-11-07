-- Prove2me | Definitions.Def_CoDecompFO_HTh
-- name    : CoDecompFO_HTh
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T20:47:47.640933+00:00
-- url     : https://prove2.me/theorems/282c58cc-2473-48d4-b8db-92bab72f3950
-- title:
--   Strategies, hypotheticals, induced hypotheticals, projections, reduced pullbacks, evaluation, and the tower
-- statement:
--   The recursive objects of the paper's full first-order case, in the reduced form.
--
--   An **$m$-strategy** on $G$ sends each point $x$ to a set of responses: pairs of a point $y$ and an $(m-1)$-strategy. It is **total** if all these sets are non-empty, at every level. The **full strategy** allows every response.
--
--   An **$m$-hypothetical** over a set $P$ is a set of hypotheses when $m=0$, and for $m>0$ assigns to each $x\in P$ a set of personalities, each a set of pairs of a point of $P$ and an $(m-1)$-hypothetical. The **induced hypothetical** $S[G]$ of a strategy has the induced hypothesis at each leaf and one personality at each point. The **projection** $f_*$ along $f:P\to Q$ collects at $x'$ the personalities of all $x$ above $x'$, projected along $f$; heads do not change. The **reduced pullback** of hypotheticals $A$ over $P$ and $B$ over $Q$ intersects heads at level $0$, and otherwise takes, for each pair of personalities at the two coordinates of $x$, all compatible pairs of responses.
--
--   **Alternating evaluation** of a hypothetical reads the personalities universally and the responses existentially; "all hypotheses satisfy $\psi$" reads both universally. The **tower** is $h_0=2^{2^q}$, $h_{m+1}=2^{w2^{wh_m}}$.
--
--   **Formalization Note** Assignments are the path to a node, not part of the type. Sets merge equal entries: this is the reduced form of ¶5.37, which Proposition 5.38 identifies with the set-level objects of ¶5.9 and ¶5.12. The full strategy and alternating evaluation are not in the paper; they carry the corrected dynamic program.
-- source:
--   Bumpus, Gomes, Larios-Jones, Turner, Co-Decompositions and FO Model Checking, arXiv:2611.04658 (held file sha256 d550d7af…), ¶5.9, p.19; ¶5.12, p.19; ¶5.15, p.20; ¶5.37, Prop. 5.38, p.24; ¶5.42, p.25; ¶5.82, p.41

import Mathlib
import Definitions.Def_CoDecompFO_Fib
import Definitions.Def_CoDecompFO_AltSat

set_option autoImplicit false

namespace CoDecompFO

open FirstOrder

/-- **`m`-strategies** on `G` (Bumpus et al., arXiv:2611.04658, held file sha256 d550d7af…, ¶5.9,
p.19, in the reduced form of ¶5.37, p.24): "Strat_0(G,β) = {β}" and "Strat_m(G,β) = ∏_{x∈G}
P(∑_{y∈G} Strat_{m−1}(G,β·x·y))". A response is a set of pairs of a point and a continuation.

**Formalization Note** The current assignment `β` is not part of the type; it is the path to the
node, passed as a list where it is needed. Proposition 5.38 (p.24) identifies the set-level objects
with the reduced ones, which is why `Set` is used and equal entries merge. -/
def Strat (G : Type) : ℕ → Type
  | 0 => Unit
  | m + 1 => G → Set (G × Strat G m)

/-- `S` has **non-empty responses** at every level (¶5.9, p.19: "the set of functions taking points x
in G to non-empty subsets of ∑_{y∈G} Strat_{m−1}(G,β·x·y)"). -/
def Strat.Total {G : Type} : (m : ℕ) → Strat G m → Prop
  | 0, _ => True
  | m + 1, S => ∀ x : G, (S x).Nonempty ∧ ∀ c ∈ S x, Strat.Total m c.2

/-- The **full strategy**: at every point, every response is allowed, followed by the full strategy.
It is not in the paper; it is the object of the correction of Observation 5.79. -/
def Strat.full (G : Type) : (m : ℕ) → Strat G m
  | 0 => ()
  | m + 1 => fun _ => Set.range fun y : G => (y, Strat.full G m)

/-- **`m`-hypotheticals** over the point set `P` (¶5.12, p.19, in the reduced form of ¶5.37, p.24):
"HTh_0(G,β) = 2^{Hyp(G,β)}" and "HTh_m(G,β) = ∏_{x∈G} P(P(∑_{y∈G} HTh_{m−1}(G,β·x·y)))".

**Formalization Note** A hypothesis with a given underlying assignment is its head, a set of atoms on
`[k]` (proof of Theorem 4.2, p.16). The underlying assignment is the path to the leaf, so it is not
stored. Prop. 5.38 (p.24) identifies these objects with the reduced ones of ¶5.37; sets merge equal
entries, which is what Lemma 5.81 counts. -/
def HTh (σ : Sig) (P : Type) (k : ℕ) : ℕ → Type
  | 0 => Set (Set (σ.Atom k))
  | m + 1 => P → Set (Set (P × HTh σ P k m))

/-- A 0-hypothetical, as the set of hypotheses it is. -/
@[reducible] def HTh.hyps {σ : Sig} {P : Type} {k : ℕ} (A : HTh σ P k 0) : Set (Set (σ.Atom k)) := A

/-- The **induced hypothetical** `S[G]` (¶5.42, p.25: "the hypothetical whose hypotheses are all
induced on G"), relative to the assignment `l`, with one personality at each point. -/
def ind (σ : Sig) (k : ℕ) {G : Type} [σ.lang.Structure G] :
    (m : ℕ) → Strat G m → List G → HTh σ G k m
  | 0, _, l => ({atomsOf σ k l} : Set (Set (σ.Atom k)))
  | m + 1, S, l => fun x =>
      ({(fun c : G × Strat G m => (c.1, ind σ k m c.2 (l ++ [x, c.1]))) '' S x} :
        Set (Set (G × HTh σ G k m)))

/-- `H` is **induced** relative to `l`, with non-empty families at every level (¶5.15, p.20: "A
hypothetical is said to be induced if all of the hypotheses it contains are induced"; ¶5.9 for
non-empty). -/
def IsInducedTotal (σ : Sig) (k : ℕ) {G : Type} [σ.lang.Structure G] :
    (m : ℕ) → List G → HTh σ G k m → Prop
  | 0, l, H => H = ({atomsOf σ k l} : Set (Set (σ.Atom k)))
  | m + 1, l, H => ∀ x : G, (H x).Nonempty ∧ ∀ p ∈ H x, p.Nonempty ∧
      ∀ c ∈ p, IsInducedTotal σ k m (l ++ [x, c.1]) c.2

/-- The **projection** `f_*` of a hypothetical (¶5.44, p.26), reduced: the personalities at `x′` are
the responses at all points `x` above `x′`, each projected along `f`. Heads do not change
(Observation 4.15, p.12). -/
def push {σ : Sig} {k : ℕ} {P Q : Type} (f : P → Q) :
    (m : ℕ) → HTh σ P k m → HTh σ Q k m
  | 0, A => A
  | m + 1, A => fun x' =>
      {q | ∃ x p, f x = x' ∧ p ∈ A x ∧
        q = (fun c : P × HTh σ P k m => (f c.1, push f m c.2)) '' p}

/-- The **reduced pullback** of hypotheticals over a reduced adhesion (Cor. 5.71, p.36; ¶5.80, p.41): at level
`0`, the pairwise intersections of heads (pullback of heads, Lemma 4.10, p.11); at level `m+1`, for each
pair of personalities of the two coordinates of `x`, all compatible pairs of responses. -/
def pb {σ : Sig} {k : ℕ} {P Q K : Type} (g : P → K) (h : Q → K) :
    (m : ℕ) → HTh σ P k m → HTh σ Q k m → HTh σ (Fib g h) k m
  | 0, A, B => ({N | ∃ N₁ ∈ HTh.hyps A, ∃ N₂ ∈ HTh.hyps B, N = N₁ ∩ N₂} : Set (Set (σ.Atom k)))
  | m + 1, A, B => fun x =>
      {q | ∃ p₁ ∈ A x.fst, ∃ p₂ ∈ B x.snd,
        q = {c | ∃ c₁ c₂, (c.1.fst, c₁) ∈ p₁ ∧ (c.1.snd, c₂) ∈ p₂ ∧ c.2 = pb g h m c₁ c₂}}

/-- **Alternating evaluation** of a hypothetical: `eval_0(N) := N ⊨ ψ` for all hypotheses,
`eval_{m+1}(A) := ∀x′ ∀p ∈ A(x′) ∃(y′,c) ∈ p, eval_m(c)`. It is not in the paper; it replaces the root
test of the proof of Theorem 1.16 (p.41) on the full strategy's projection. -/
def eval {σ : Sig} {k : ℕ} {P : Type} (ψ : σ.lang.BoundedFormula Empty k) :
    (m : ℕ) → HTh σ P k m → Prop
  | 0, A => ∀ N ∈ HTh.hyps A, Holds ψ N
  | m + 1, A => ∀ x', ∀ p ∈ A x', ∃ c ∈ p, eval ψ m c.2

/-- **All hypotheses of `H` satisfy `ψ`** (Lemma 5.16, p.20; Lemma 5.78, p.40): every hypothesis
occurring in a 0-hypothetical of `H`. -/
def AllHyp {σ : Sig} {k : ℕ} {P : Type} (ψ : σ.lang.BoundedFormula Empty k) :
    (m : ℕ) → HTh σ P k m → Prop
  | 0, A => ∀ N ∈ HTh.hyps A, Holds ψ N
  | m + 1, A => ∀ x', ∀ p ∈ A x', ∀ c ∈ p, AllHyp ψ m c.2

/-- The tower of ¶5.82 (p.41): `h_0 = 2^{2^q}` and `h_{m+1} = 2^{w 2^{w h_m}}`; at `m = ℓ` it has the
printed `2ℓ+2` exponential layers. -/
def tower (w q : ℕ) : ℕ → ℕ
  | 0 => 2 ^ 2 ^ q
  | m + 1 => 2 ^ (w * 2 ^ (w * tower w q m))

end CoDecompFO


