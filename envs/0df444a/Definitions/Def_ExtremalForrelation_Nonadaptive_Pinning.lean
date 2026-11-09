-- Prove2me | Definitions.Def_ExtremalForrelation_Nonadaptive_Pinning
-- name    : ExtremalForrelation_Nonadaptive_Pinning
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:56:30.098663+00:00
-- url     : https://prove2.me/theorems/0570f786-1c11-4fc8-86e5-afb41b874f69
-- title:
--   Queried cosets, anchors, the pinning graph $H_\tau$, compatibility, $E(\pi)$, $L_s$, matching probabilities $p_{I,J}(H)$ and $\Pi_T$
-- statement:
--   Fix a query set $Q$ and a subspace $K$ of $\mathbb F_2^n$. A transcript $\tau$ records answers $f(x),g(x)$ for $x\in Q$.
--
--   1. **Queried cosets.** $F$ is the set of cosets of $K$ containing a query and $G$ the set of cosets of $K^\perp$ containing a query. The **anchor** of $C\in F$ (or $D\in G$) is a fixed query in it, chosen from $Q$ and $K$ only (the smallest as a binary number); the **anchor answers** of $\tau$ are $(f(x_C))_{C\in F}$ and $(g(y_D))_{D\in G}$.
--   2. **Pinning graph (Definition 7).** $H_\tau$ is the bipartite graph between the cosets of $K$ and the cosets of $K^\perp$ in which $C$ and $D$ are adjacent iff
--   $$f(x)+f(x')=\langle x+x',y\rangle\ \text{for all queries }x,x'\in C\text{ and all points }y\in D,$$
--   $$g(y)+g(y')=\langle x,y+y'\rangle\ \text{for all queries }y,y'\in D\text{ and all points }x\in C,$$
--   with $f,g$ read from $\tau$. The two sides are disjoint copies, even if a coset of $K$ is also a coset of $K^\perp$.
--   3. **Matchings.** A perfect matching of a bipartite graph $H$ is a bijection $\pi$ with $(C,\pi(C))\in H$ for all $C$. The matching revealed by the queries is
--   $$E(\pi)=\{(C,\pi(C)) : C\in F,\ \pi(C)\in G\}. \tag{9}$$
--   4. **Compatibility (Definition 8).** $\pi\bowtie\tau$ means $\pi$ is a perfect matching of $H_\tau$. $(\pi,s)\bowtie\tau$ means moreover
--   $$f(x_C)+g(y_D)=\langle x_C,y_D\rangle+s\quad\text{for every }(C,D)\in E(\pi). \tag{10}$$
--   5. **Likelihood ratio.** $L_s(\tau)=\mu_s(\tau\mid K)/\rho(\tau\mid K)$ (13), used where $\rho(\tau\mid K)>0$.
--   6. **Matching probabilities.** For $I\subseteq F$, $J\subseteq G$, $p_{I,J}(H)=\Pr_{\pi\bowtie H}[\pi(I)=J]$ (16), with $\pi$ uniform among all perfect matchings of $H$. $\Pi_T$ is the set of perfect matchings of $H$ containing every edge of $T$. A partial matching is a set of edges no two of which share an endpoint.
--
--   These objects carry the paper's §§3.4–3.6 argument.
--
--   **Formalization Note.** Function values of $\tau$ are read by `tval`, which is $(0,0)$ off $Q$ but is only consulted at queries. Matching probabilities are counting ratios over the perfect matchings of $H$ (they are $0/0=0$ when $H$ has none; every theorem using them either weights them by $\rho(\tau\mid K)$ or assumes $\rho(\tau\mid K)>0$). The sum $\sum_{I\subseteq F,J\subseteq G,|I|=|J|\ge1}p_{I,J}(H)^2$ is `sumSqMatchProb`.
-- source:
--   Clément Canonne, Kenny Chen, Julian Mestre, STOC 2027 submission #61 (October 2026), §3.4 pp. 12–15 (F, G, anchors, Definition 7, eqs. (9), (10), Definition 8, eq. (13)), §3.5 p. 15 eq. (16), §3.6 p. 18 (Π_T), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/61.pdf

import Mathlib
import Definitions.Def_ExtremalForrelation_Nonadaptive_Instance

open Classical

noncomputable section

namespace ExtremalForrelation.Nonadaptive

/-!
# Queried cosets, anchors, pinning graphs, compatibility and matching probabilities

Canonne–Chen–Mestre, STOC 2027 submission #61 (October 2026), §3.4 pp. 12–15
(`F`, `G`, anchors, Definition 7, equation (9), equation (10), Definition 8, equation (13)),
§3.5 p. 15 (equation (16)), §3.6 p. 18 (`Π_T`).

Throughout, `Q` is a fixed query set and `K` a fixed subspace. Cosets of `K` are elements of
`V n ⧸ K` and cosets of `K^⊥` elements of `V n ⧸ orth K`: the two sides of every bipartite
graph are these two (distinct) types, even when the underlying sets of cosets overlap.
A bipartite graph is a relation `H : V n ⧸ K → V n ⧸ orth K → Prop`; a perfect matching of `H`
is a bijection `π` with `H C (π C)` for every `C`.
-/

/-- The answer pair recorded by `τ` at a point `x` (`(0, 0)` off `Q`; only used on `Q`). -/
def tval {n : ℕ} {Q : Finset (V n)} (τ : Transcript Q) (x : V n) : ZMod 2 × ZMod 2 :=
  if h : x ∈ Q then τ ⟨x, h⟩ else (0, 0)

/-- `F`: the cosets of `K` containing a query. -/
def Fset {n : ℕ} (Q : Finset (V n)) (K : Submodule (ZMod 2) (V n)) : Finset (V n ⧸ K) :=
  Q.image (fun x => Submodule.Quotient.mk x)

/-- `G`: the cosets of `K^⊥` containing a query. -/
def Gset {n : ℕ} (Q : Finset (V n)) (K : Submodule (ZMod 2) (V n)) : Finset (V n ⧸ orth K) :=
  Q.image (fun x => Submodule.Quotient.mk x)

/-- The anchor of a coset `c` of `W`: a fixed query in `Q ∩ c` chosen from `Q` and `W` only
(the smallest one as a binary number). -/
def anchor {n : ℕ} (Q : Finset (V n)) (W : Submodule (ZMod 2) (V n)) (c : V n ⧸ W) : V n :=
  minBin (Q.filter (fun x => Submodule.Quotient.mk x = c))

/-- The anchor answers `((f(x_i))_{i ∈ F}, (g(y_j))_{j ∈ G})` recorded by `τ`. -/
def anchorAns {n : ℕ} (Q : Finset (V n)) (K : Submodule (ZMod 2) (V n)) (τ : Transcript Q) :
    (Fset Q K → ZMod 2) × (Gset Q K → ZMod 2) :=
  (fun C => (tval τ (anchor Q K C.1)).1, fun D => (tval τ (anchor Q (orth K) D.1)).2)

/-- Definition 7 (p. 13): the pinning graph `H_τ`. `C` and `D` are adjacent iff
`f(x) + f(x') = ⟨x + x', y⟩` for all queries `x, x' ∈ C` and all points `y ∈ D`, and
`g(y) + g(y') = ⟨x, y + y'⟩` for all queries `y, y' ∈ D` and all points `x ∈ C`, with the
function values read from `τ`. -/
def pinGraph {n : ℕ} (Q : Finset (V n)) (K : Submodule (ZMod 2) (V n)) (τ : Transcript Q)
    (C : V n ⧸ K) (D : V n ⧸ orth K) : Prop :=
  (∀ x ∈ Q, ∀ x' ∈ Q, Submodule.Quotient.mk x = C → Submodule.Quotient.mk x' = C →
      ∀ y : V n, Submodule.Quotient.mk y = D → (tval τ x).1 + (tval τ x').1 = dot (x + x') y) ∧
  (∀ y ∈ Q, ∀ y' ∈ Q, Submodule.Quotient.mk y = D → Submodule.Quotient.mk y' = D →
      ∀ x : V n, Submodule.Quotient.mk x = C → (tval τ y).2 + (tval τ y').2 = dot x (y + y'))

/-- `π ⋈ H`: `π` is a perfect matching of the bipartite graph `H` (Definition 8, p. 13). -/
def IsPM {n : ℕ} {K : Submodule (ZMod 2) (V n)} (H : V n ⧸ K → V n ⧸ orth K → Prop)
    (π : (V n ⧸ K) ≃ (V n ⧸ orth K)) : Prop :=
  ∀ C, H C (π C)

/-- Equation (9), p. 13: `E(π) = {(i, π(i)) : i ∈ F, π(i) ∈ G}`. -/
def Eset {n : ℕ} (Q : Finset (V n)) (K : Submodule (ZMod 2) (V n))
    (π : (V n ⧸ K) ≃ (V n ⧸ orth K)) : Finset ((V n ⧸ K) × (V n ⧸ orth K)) :=
  ((Fset Q K).filter (fun C => π C ∈ Gset Q K)).image (fun C => (C, π C))

/-- Equation (10), p. 13, on a vector of anchor answers `a`:
`a_F(i) + a_G(j) = ⟨x_i, y_j⟩ + s` for every `(i, j) ∈ E(π)`. -/
def Sat10 {n : ℕ} (Q : Finset (V n)) (K : Submodule (ZMod 2) (V n))
    (π : (V n ⧸ K) ≃ (V n ⧸ orth K)) (s : ZMod 2)
    (a : (Fset Q K → ZMod 2) × (Gset Q K → ZMod 2)) : Prop :=
  ∀ (C : Fset Q K) (D : Gset Q K), π C.1 = D.1 →
    a.1 C + a.2 D = dot (anchor Q K C.1) (anchor Q (orth K) D.1) + s

/-- `π ⋈ τ` (Definition 8): `π` is a perfect matching of `H_τ`. -/
def Compat {n : ℕ} (Q : Finset (V n)) (K : Submodule (ZMod 2) (V n))
    (π : (V n ⧸ K) ≃ (V n ⧸ orth K)) (τ : Transcript Q) : Prop :=
  IsPM (pinGraph Q K τ) π

/-- `(π, s) ⋈ τ` (Definition 8): `π ⋈ τ` and `τ` satisfies (10). -/
def CompatS {n : ℕ} (Q : Finset (V n)) (K : Submodule (ZMod 2) (V n))
    (π : (V n ⧸ K) ≃ (V n ⧸ orth K)) (s : ZMod 2) (τ : Transcript Q) : Prop :=
  Compat Q K π τ ∧ Sat10 Q K π s (anchorAns Q K τ)

/-- Equation (13), p. 15: `L_s(τ) = μ_s(τ | K) / ρ(τ | K)` (used only where `ρ(τ | K) > 0`). -/
def Lratio {n : ℕ} (Q : Finset (V n)) (K : Submodule (ZMod 2) (V n)) (s : ZMod 2)
    (τ : Transcript Q) : ℝ :=
  muK Q s K τ / rhoK Q K τ

/-- The perfect matchings `Π` of `H`. -/
def PMs {n : ℕ} {K : Submodule (ZMod 2) (V n)} (H : V n ⧸ K → V n ⧸ orth K → Prop) :
    Finset ((V n ⧸ K) ≃ (V n ⧸ orth K)) :=
  Finset.univ.filter (fun π => IsPM H π)

/-- `Π_T` (p. 18): the perfect matchings of `H` containing every edge of `T`. -/
def PiT {n : ℕ} {K : Submodule (ZMod 2) (V n)} (H : V n ⧸ K → V n ⧸ orth K → Prop)
    (T : Finset ((V n ⧸ K) × (V n ⧸ orth K))) : Finset ((V n ⧸ K) ≃ (V n ⧸ orth K)) :=
  (PMs H).filter (fun π => ∀ e ∈ T, π e.1 = e.2)

/-- Equation (16), p. 15: `p_{I,J}(H) = Pr_{π ⋈ H}[π(I) = J]`, for `π` uniform among the
perfect matchings of `H`. -/
def matchProb {n : ℕ} {K : Submodule (ZMod 2) (V n)} (H : V n ⧸ K → V n ⧸ orth K → Prop)
    (I : Finset (V n ⧸ K)) (J : Finset (V n ⧸ orth K)) : ℝ :=
  (((PMs H).filter (fun π => I.image π = J)).card : ℝ) / (PMs H).card

/-- `∑_{I ⊆ F, J ⊆ G, |I| = |J| ≥ 1} p_{I,J}(H)²` (Lemmas 9 and 11). -/
def sumSqMatchProb {n : ℕ} (Q : Finset (V n)) (K : Submodule (ZMod 2) (V n))
    (H : V n ⧸ K → V n ⧸ orth K → Prop) : ℝ :=
  ∑ I ∈ (Fset Q K).powerset, ∑ J ∈ (Gset Q K).powerset,
    if 1 ≤ I.card ∧ I.card = J.card then matchProb H I J ^ 2 else 0

/-- A partial matching: no two distinct edges share an endpoint. -/
def IsPartialMatching {α β : Type*} (T : Finset (α × β)) : Prop :=
  ∀ e ∈ T, ∀ e' ∈ T, (e.1 = e'.1 ↔ e.2 = e'.2)

end ExtremalForrelation.Nonadaptive


