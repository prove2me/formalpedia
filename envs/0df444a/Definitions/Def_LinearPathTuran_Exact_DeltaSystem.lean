-- Prove2me | Definitions.Def_LinearPathTuran_Exact_DeltaSystem
-- name    : LinearPathTuran_Exact_DeltaSystem
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T19:21:13.107627+00:00
-- url     : https://prove2.me/theorems/6e7c6152-af81-414b-93f0-08553f4b45bf
-- title:
--   pp. 4–8 — Δ-systems, k-partite and (k,s)-homogeneous families, rank, type 1, kernel graphs, blowups
-- statement:
--   This file fixes the vocabulary of the delta-system method used in §§3–4 of Füredi, Jiang and Seiver.
--
--   1. **Stars (p. 4).** Sets $F_1,\dots,F_s$ form an *$s$-star* (Δ-system) with *kernel* $A$ if $F_i\cap F_j=A$ for all $i<j$; the $F_i$ are the *petals*. The *kernel degree* $\deg^*_{\mathcal F}(W)$ (p. 7) is the largest $s$ such that $\mathcal F$ contains an $s$-star with kernel $W$.
--   2. **$k$-partite families and patterns (p. 4).** $\mathcal F\subseteq\binom{[n]}{k}$ is *$k$-partite* with parts $X_1,\dots,X_k$ (a partition of $[n]$) if $|F\cap X_i|=1$ for every $F\in\mathcal F$ and $i\in[k]$. The *pattern* of $S\subseteq[n]$ is $\Pi(S)=\{i: S\cap X_i\neq\emptyset\}$.
--   3. **Intersection structure (p. 4).** $\mathcal I(F,\mathcal F)=\{F\cap F' : F'\in\mathcal F,\ F'\neq F\}$.
--   4. **Homogeneous families (Definition 3.2, p. 5).** $\mathcal F^*$ is *$(k,s)$-homogeneous with intersection pattern $\mathcal J$* if it is $k$-partite with a $k$-partition $(X_1,\dots,X_k)$; $\mathcal J$ is a family of proper subsets of $[k]$ with $\Pi(\mathcal I(F,\mathcal F^*))=\mathcal J$ for every $F\in\mathcal F^*$; $\mathcal J$ is closed under intersection; and for every $F\in\mathcal F^*$ and every $A\in\mathcal I(F,\mathcal F^*)$ there is an $s$-star in $\mathcal F^*$ containing $F$ with kernel $A$.
--   5. **Rank and type (p. 5, Definition 3.5).** For a family $\mathcal L$ of subsets of $[k]$,
--   $$r(\mathcal L)=\min\{|D| : D\subseteq[k],\ \nexists B\in\mathcal L,\ D\subseteq B\}.$$
--   A family $\mathcal L$ of proper subsets of $[k]$ of rank $k-1$ is of *type 1* if some $x\in[k]$ has $[k]\setminus\{x\}\notin\mathcal L$ while $[k]\setminus\{y\}\in\mathcal L$ for all $y\neq x$; otherwise it is of *type 2*.
--   6. **Kernel graph (Definition 4.1, p. 7).** The kernel graph of $\mathcal F$ with threshold $s$ is the graph on $[n]$ in which $xy$ is an edge iff $\deg^*_{\mathcal F}(\{x,y\})\ge s$.
--   7. **Blowups (p. 6).** For a graph $H$, the *$k$-blowup* $H^{(k)}$ replaces each edge $xy$ by a $k$-set $E_{xy}$ consisting of $x$, $y$ and $k-2$ new vertices, the new parts $E_{xy}\setminus\{x,y\}$ of distinct edges being disjoint; $H$ is its *skeleton*.
--   8. **Centre graph (p. 8).** Given a choice of a vertex $c(F)\in F$ for each member $F$, the graph on $[n]$ whose edges are the pairs $\{c(F),y\}$ with $F\in\mathcal F$, $y\in F\setminus\{c(F)\}$. When $c(F)$ is the central element of $F$ this is the paper's graph $H'$, the underlying simple graph of the $(k,s)$-homogeneous kernel graph.
--
--   **Formalization Note** The $k$-partition is a part map `χ : Fin n → Fin k` with $X_i=\chi^{-1}(i)$; $k$-partiteness forces every member to have exactly $k$ elements. A star is a finset `𝒮` of members (so its petals are distinct) with $A$ contained in every petal and any two distinct petals meeting exactly in $A$; for $s=1$ this makes "a 1-star with kernel $A$" a member containing $A$. `HasStar 𝓕 A s` means $\deg^*_{\mathcal F}(A)\ge s$. The rank is an `sInf` over natural numbers; when no member of $\mathcal L$ is all of $[k]$ (always the case for intersection patterns) the set is nonempty ($D=[k]$) and the value is the true minimum, while if $[k]\in\mathcal L$ the value would be the junk $0$. `IsType1` is the type-1 condition; "type 2" is written as rank $k-1$ and not type 1. `ContainsBlowupOn 𝓕 H` is a copy of $H^{(k)}$ in $\mathcal F$ whose skeleton is $H$ itself: the extra vertices of each $E_{xy}$ avoid every non-isolated vertex of $H$. `ContainsBlowup 𝓕 T` for a graph $T$ on $p$ vertices embeds $T$ into $[n]$ first; for graphs without isolated vertices (trees with at least one edge) this is exactly "$T^{(k)}\subseteq\mathcal F$".
-- source:
--   Füredi, Jiang and Seiver, Exact solution of the hypergraph Turán problem for k-uniform linear paths, arXiv:1108.1247v1, pp. 4–5 (§3, Δ-systems, k-partite, Π, I(F,F), Lemma 3.1 items 2–5, Definition 3.2, rank, Definition 3.5), p. 6 (k-blowup), p. 7 (kernel degree, Definition 4.1), p. 8 (H′)

import Mathlib

namespace LinearPathTuran.Exact

open Finset

variable {n k : ℕ}

/-- `𝒮` is a star (Δ-system) with kernel `A` (p. 4): `A` lies in every petal and any two distinct
petals meet exactly in `A`. The petals are the members of the finset `𝒮`, hence distinct. -/
def IsStar (𝒮 : Finset (Finset (Fin n))) (A : Finset (Fin n)) : Prop :=
  (∀ G ∈ 𝒮, A ⊆ G) ∧ ∀ G ∈ 𝒮, ∀ G' ∈ 𝒮, G ≠ G' → G ∩ G' = A

/-- `𝓕` contains an `s`-star with kernel `A`, i.e. `deg*_𝓕(A) ≥ s` (p. 7). -/
def HasStar (𝓕 : Finset (Finset (Fin n))) (A : Finset (Fin n)) (s : ℕ) : Prop :=
  ∃ 𝒮 ⊆ 𝓕, #𝒮 = s ∧ IsStar 𝒮 A

/-- `𝓕` is `k`-partite with parts `X_i = χ⁻¹(i)` (p. 4): every member meets every part in exactly
one vertex. -/
def IsKPartite (𝓕 : Finset (Finset (Fin n))) (χ : Fin n → Fin k) : Prop :=
  ∀ F ∈ 𝓕, ∀ i : Fin k, #(F.filter (fun v => χ v = i)) = 1

/-- The pattern `Π(S) = {i : S ∩ X_i ≠ ∅}` of `S` with respect to the parts `X_i = χ⁻¹(i)` (p. 4). -/
def pattern (χ : Fin n → Fin k) (S : Finset (Fin n)) : Finset (Fin k) := S.image χ

/-- The intersection structure `I(F, 𝓕) = {F ∩ F' : F' ∈ 𝓕, F' ≠ F}` (p. 4). -/
def interStruct (𝓕 : Finset (Finset (Fin n))) (F : Finset (Fin n)) : Finset (Finset (Fin n)) :=
  (𝓕.erase F).image (fun F' => F ∩ F')

/-- `𝓕` is `(k, s)`-homogeneous with intersection pattern `J` and `k`-partition `χ`
(Definition 3.2 = items (2)–(5) of Lemma 3.1, pp. 4–5). -/
def IsHomogeneous (s : ℕ) (𝓕 : Finset (Finset (Fin n))) (χ : Fin n → Fin k)
    (J : Finset (Finset (Fin k))) : Prop :=
  IsKPartite 𝓕 χ ∧ (∀ A ∈ J, A ≠ univ) ∧
  (∀ F ∈ 𝓕, (interStruct 𝓕 F).image (pattern χ) = J) ∧
  (∀ A ∈ J, ∀ B ∈ J, A ∩ B ∈ J) ∧
  (∀ F ∈ 𝓕, ∀ A ∈ interStruct 𝓕 F, ∃ 𝒮 ⊆ 𝓕, #𝒮 = s ∧ F ∈ 𝒮 ∧ IsStar 𝒮 A)

/-- The rank `r(L) = min{|D| : D ⊆ [k], no member of L contains D}` (p. 5). When `univ ∉ L` the set
is nonempty (`D = univ`) and this is the true minimum; otherwise `sInf ∅ = 0` (never used so). -/
noncomputable def rank (L : Finset (Finset (Fin k))) : ℕ :=
  sInf {d | ∃ D : Finset (Fin k), #D = d ∧ ∀ B ∈ L, ¬ D ⊆ B}

/-- `L` is of type 1 (Definition 3.5, p. 5; used together with `rank L = k - 1`): some `x` has
`[k] \ {x} ∉ L` while `[k] \ {y} ∈ L` for every `y ≠ x`. -/
def IsType1 (L : Finset (Finset (Fin k))) : Prop :=
  ∃ x : Fin k, univ.erase x ∉ L ∧ ∀ y, y ≠ x → univ.erase y ∈ L

/-- The kernel graph of `𝓕` with threshold `s` (Definition 4.1, p. 7): `xy` is an edge iff
`x ≠ y` and `deg*_𝓕({x, y}) ≥ s`. -/
def kernelGraph (𝓕 : Finset (Finset (Fin n))) (s : ℕ) : SimpleGraph (Fin n) where
  Adj x y := x ≠ y ∧ HasStar 𝓕 {x, y} s
  symm := ⟨fun x y h => ⟨h.1.symm, by rw [Finset.pair_comm]; exact h.2⟩⟩
  loopless := ⟨fun x h => h.1 rfl⟩

/-- `𝓕` contains a copy of the `k`-blowup `H^(k)` whose skeleton is `H` itself (p. 6): every edge
`xy` of `H` is replaced by a member `E x y ∈ 𝓕` containing `x` and `y` whose other vertices are new
(off every vertex of `H`), and the new parts of distinct edges are disjoint. -/
def ContainsBlowupOn (𝓕 : Finset (Finset (Fin n))) (H : SimpleGraph (Fin n)) : Prop :=
  ∃ E : Fin n → Fin n → Finset (Fin n),
    (∀ x y, H.Adj x y → E x y = E y x ∧ E x y ∈ 𝓕 ∧ x ∈ E x y ∧ y ∈ E x y ∧
        ∀ z ∈ E x y, z = x ∨ z = y ∨ z ∉ H.support) ∧
    (∀ x y x' y', H.Adj x y → H.Adj x' y' → s(x, y) ≠ s(x', y') →
        Disjoint (E x y \ {x, y}) (E x' y' \ {x', y'}))

/-- `𝓕` contains a copy of `T^(k)` for a graph `T` on `Fin p`, its vertices embedded by `φ`. -/
def ContainsBlowup {p : ℕ} (𝓕 : Finset (Finset (Fin n))) (T : SimpleGraph (Fin p)) : Prop :=
  ∃ φ : Fin p ↪ Fin n, ContainsBlowupOn 𝓕 (T.map φ)

/-- The centre graph of `𝓕` for a choice `c F` of a vertex of each member (p. 8, the graph `H'`
when `c F` is the central element of `F`): `x ~ y` iff `x ≠ y` and some member `F` has
`c F = x, y ∈ F` or `c F = y, x ∈ F`. -/
def centreGraph (𝓕 : Finset (Finset (Fin n))) (c : Finset (Fin n) → Fin n) :
    SimpleGraph (Fin n) where
  Adj x y := x ≠ y ∧ ∃ F ∈ 𝓕, (c F = x ∧ y ∈ F) ∨ (c F = y ∧ x ∈ F)
  symm := ⟨fun x y h => ⟨h.1.symm, by
    obtain ⟨F, hF, h'⟩ := h.2
    exact ⟨F, hF, h'.symm⟩⟩⟩
  loopless := ⟨fun x h => h.1 rfl⟩

end LinearPathTuran.Exact


