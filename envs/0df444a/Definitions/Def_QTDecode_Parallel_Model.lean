-- Prove2me | Definitions.Def_QTDecode_Parallel_Model
-- name    : QTDecode_Parallel_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T06:52:10.804386+00:00
-- url     : https://prove2.me/theorems/bb05f1ea-46a2-4ec8-b955-c8839de30a65
-- title:
--   Algorithm 3, pp. 17–20 — the parallel mismatch decomposition; decompositions, norm, active, exceptional and ordinary vertices (§§3, 5); the square graphs (p. 10)
-- statement:
--   This file adds to the published quantum Tanner code layer (`QAlgorithms_Defs_TannerDecoder`) the objects of Leverrier and Zémor's analysis of the **parallel decoder**. Throughout, $G$ is a finite group, $A,B\subseteq G$, the vertex set is $V=V_{00}\cup V_{01}\cup V_{10}\cup V_{11}$ with $V_{ij}=G\times\{ij\}$, the squares $Q$ are indexed by $G\times A\times B$ (the square $(g,a,b)$ is $\{(g,00),(ag,01),(gb,10),(agb,11)\}$), and every vertex $v$ sees its $Q$-neighbourhood $Q(v)\cong A\times B$. A vector $x\in\mathbb F_2^{A\times B}$ has columns indexed by $b\in B$ and rows indexed by $a\in A$; $\|c\|$ is the number of non-zero columns and $\|r\|$ the number of non-zero rows. Only $\sigma_x$-type errors are treated, with local codes $C_A$, $C_B$.
--
--   1. **Parallel decoding (Algorithm 3, pp. 17, 20).** Given the current mismatch $\hat Z\in\mathbb F_2^Q$, a word $x$ on $Q(v)$ is *admissible* if it is a non-zero codeword of the dual tensor code $C_A\otimes\mathbb F_2^B+\mathbb F_2^A\otimes C_B$ and
--   $$|\hat Z|-|\hat Z+x|\ \ge\ |x|/2 .$$
--   The *parallel choice* of $v$ is $(c_v,r_v)=(0,0)$ if nothing is admissible, and otherwise a decomposition $x_v=c_v+r_v$ ($c_v\in C_A\otimes\mathbb F_2^B$, $r_v\in\mathbb F_2^A\otimes C_B$) of an admissible $x_v$ of **maximum weight** $|x_v|$, with $\|c_v\|+\|r_v\|$ minimum. A *parallel substep* on $V_{ij}$ lets every $v\in V_{ij}$ choose against the substep's starting mismatch (the $Q(v)$, $v\in V_{ij}$, partition $Q$) and applies all updates $\hat C_j\mathrel{+}=c_v$, $\hat R_i\mathrel{+}=r_v$, $\hat Z\mathrel{+}=x_v$ at once. A *round* is the four substeps on $V_{00},V_{01},V_{10},V_{11}$ in this order, and a *run* from $Z$ starts at $(\hat C,\hat R,\hat Z)=(0,0,Z)$ and performs rounds forever (every sequence of admissible choices is a run).
--   2. **Decompositions (eqs. (4)–(5), p. 19; §3, pp. 12–13).** A decomposition of $Z$ is $Z=C_0+R_0+C_1+R_1$ where every column of $C_j$ (a column of $Q(v)$, $v\in V_{0j}$) is a codeword of $C_A$ and every row of $R_i$ (a row of $Q(v)$, $v\in V_{i0}$) a codeword of $C_B$. Its norm $\|C_0\|+\|R_0\|+\|C_1\|+\|R_1\|$ counts the non-zero columns and rows; a decomposition is *minimum* if no decomposition of $Z$ has smaller norm. A *representation* of $x\in\mathcal C_1$ is a decomposition of $0$ with $x=C_1+R_0$ (hence $x=C_0+R_1$), and $x^0:=C_0+R_0=C_1+R_1$; a representation of $y$ as a codeword on $\mathcal G^\square_0$ is a decomposition of $0$ with $y=C_0+R_0$.
--   3. **Active, exceptional and ordinary vertices (pp. 14, 19, 21).** For a decomposition, $v\in V_{ij}$ is *active* if $C_j+R_i$ is non-zero on $Q(v)$; $S_{ij}$ is the set of active vertices of $V_{ij}$. With $c_v$, $r_v$ the restrictions of $C_j$, $R_i$ to $Q(v)$, an active $v$ is *exceptional* (for $\alpha$, $\Delta$) if $\|c_v\|+\|r_v\|\ge\alpha\Delta$ and *ordinary* otherwise; $S^e_{ij}$ is the set of exceptional vertices of $S_{ij}$. The set $T_{\mathrm{col}}(i,j)\subseteq V_{ij}$ consists of the vertices whose $Q(v)$ carries a column on which $C_j$ is non-zero and which is shared with an ordinary vertex $w\in V_{\bar\imath j}$ (its B-neighbour across that column); $T_{\mathrm{row}}(i,j)\subseteq S_{ij}$ consists of the active vertices whose $Q(v)$ carries a row on which $R_i$ is non-zero and which is shared with an ordinary vertex of $V_{i\bar\jmath}$.
--   4. **The sequential decoder (pp. 21, 26).** It is *stalled* at $Z$ with parameter $\varepsilon$ if no vertex $v$ and non-zero dual tensor codeword $x_v$ on $Q(v)$ satisfy $|Z|-|Z+x_v|\ge(1-\varepsilon)|x_v|$; it *converges* from a state if every finite run of Algorithm 2 from that state that has not reached $\hat Z=0$ can be extended by one more step.
--   5. **Codes and graphs.** $\mathcal C_1^\perp$ is the span of the codewords of $C_A^\perp\otimes C_B^\perp$ placed on the $Q(v)$, $v\in V_1=V_{01}\cup V_{10}$ (the $\sigma_z$-generators, p. 11). $\mathcal G^\square_0$ (on $V_{00}\cup V_{11}$) and $\mathcal G^\square_1$ (on $V_{01}\cup V_{10}$) put one edge between two vertices for every square containing both (p. 10). Finally $|x\cap y|$ is the number of coordinates where both binary vectors are non-zero.
--
--   These objects are shared by all the lemmas of the mission: the distance analysis of §3 (representations, Lemmas 7–11, Theorem 9) and the decoder analysis of §§5–6 (Lemmas 14–19, Theorems 12 and 20).
--
--   **Formalization Note** The vertex $(g,ij)$ is `(g, (i, j)) : G × (Bool × Bool)`, as in the published layer, and decoder states reuse its `SeqDecState` (`C b` $=\hat C_b$, `R b` $=\hat R_b$). Sets of vertices of $V_{ij}$ are `Finset G`. The norm of a decomposition counts columns of $C_j$ at $V_{0j}$ and rows of $R_i$ at $V_{i0}$, which counts every column and row of the complex exactly once (p. 19). A parallel vertex compares against the substep's starting mismatch; since the $Q(v)$, $v\in V_{ij}$, are disjoint, this is the local view at its turn. `IsParAdmissible` requires $x\ne0$, as the text on p. 17 and Algorithm 3 line 6 do.
-- source:
--   Leverrier and Zémor, Decoding quantum Tanner codes, arXiv:2208.05537v3, pp. 17–20, Algorithm 3 and its description (p. 17); p. 19, eqs. (4)–(5); pp. 12–14 (representations, norm, S_ij, exceptional vertices); p. 15 and p. 23 (sets T); p. 21 (stalled decoder, ordinary columns); p. 26 (convergence); p. 10 (square graphs); p. 11 (σz generators)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_TannerDecoder

/-!
# Decoding quantum Tanner codes: the parallel decoder, decompositions, active and exceptional vertices

A. Leverrier, G. Zémor, *Decoding quantum Tanner codes*, arXiv:2208.05537v3, cited "p. N"
(printed page = PDF page).

Built on the published layer `QAlgorithms_Defs_TannerDecoder` (vertices `G × (Bool × Bool)`, where
`(g, (i, j))` is `(g, ij) ∈ V_ij`; squares `G × A × B`; local views `qtLocalView`, `qtPush`; the
sequential decoder state `SeqDecState` with `C b = Ĉ_b`, `R b = R̂_b`). Only `σ_x`-type errors are
treated (local codes `C_A`, `C_B`), as in the paper (pp. 9, 21, 24, 26).

Columns of `Q(v)`, `v ∈ V_ij`, are the B-edges of layer `j` (shared between `V_0j` and `V_1j`); rows
are the A-edges of layer `i` (shared between `V_i0` and `V_i1`) (p. 11). `Ĉ_j` collects column
codewords, `R̂_i` row codewords.
-/

namespace QTDecode.Parallel

open QAlgorithms

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G] {A B : Finset G}

/-! ### Supports -/

/-- `|x ∩ y|`: the number of coordinates on which both binary vectors are non-zero (the paper
identifies a binary vector with its support, p. 21). -/
def interWeight {ι : Type*} [Fintype ι] (x y : ι → ZMod 2) : ℕ :=
  hammingNorm (x * y)

/-! ### Algorithm 3 (parallel mismatch decomposition), pp. 17, 20 -/

/-- p. 17 and Algorithm 3 line 6, p. 20: `x` is a non-zero dual tensor codeword on `Q(v)` whose flip
lowers the weight of the current mismatch `Ẑ` by at least `|x|/2`. -/
def IsParAdmissible (CA : Submodule (ZMod 2) (A → ZMod 2)) (CB : Submodule (ZMod 2) (B → ZMod 2))
    (Z : G × A × B → ZMod 2) (v : G × (Bool × Bool)) (x : A × B → ZMod 2) : Prop :=
  x ∈ dualTensorCode CA CB ∧ x ≠ 0 ∧
    (hammingNorm x : ℝ) / 2 ≤ (hammingNorm Z : ℝ) - (hammingNorm (Z + qtPush v x) : ℝ)

/-- p. 17 and Algorithm 3 line 7, p. 20: the local choice `(c_v, r_v)` of the vertex `v` against the
mismatch `Ẑ`: zero if no admissible `x_v` exists; otherwise `x_v = c_v + r_v` is admissible, of
maximum weight `|x_v|` among admissible choices, and decomposed with `‖c_v‖ + ‖r_v‖` minimum. -/
def IsParChoice (CA : Submodule (ZMod 2) (A → ZMod 2)) (CB : Submodule (ZMod 2) (B → ZMod 2))
    (Z : G × A × B → ZMod 2) (v : G × (Bool × Bool)) (c r : A × B → ZMod 2) : Prop :=
  c ∈ columnCode CA B ∧ r ∈ rowCode A CB ∧
  ((∀ x, ¬ IsParAdmissible CA CB Z v x) → c = 0 ∧ r = 0) ∧
  ((∃ x, IsParAdmissible CA CB Z v x) →
     IsParAdmissible CA CB Z v (c + r) ∧
     (∀ x, IsParAdmissible CA CB Z v x → hammingNorm x ≤ hammingNorm (c + r)) ∧
     (∀ c' ∈ columnCode CA B, ∀ r' ∈ rowCode A CB, c' + r' = c + r →
        nonzeroCols c + nonzeroRows r ≤ nonzeroCols c' + nonzeroRows r'))

/-- p. 17, Algorithm 3 lines 5–7: one parallel substep on `V_ij`. Every `v = (g, ij)` makes its
choice against the substep's starting mismatch (the `Q(v)`, `v ∈ V_ij`, partition the squares, so
this is the local view of `Ẑ` at `v`'s turn), and all updates `Ĉ_j += c_v`, `R̂_i += r_v`,
`Ẑ += c_v + r_v` are applied at once. -/
def IsParSubstep (CA : Submodule (ZMod 2) (A → ZMod 2)) (CB : Submodule (ZMod 2) (B → ZMod 2))
    (ij : Bool × Bool) (s s' : SeqDecState (G × A × B)) : Prop :=
  ∃ c r : G → A × B → ZMod 2, (∀ g, IsParChoice CA CB s.Z (g, ij) (c g) (r g)) ∧
    s' = ⟨Function.update s.C ij.2 (s.C ij.2 + ∑ g, qtPush (g, ij) (c g)),
          Function.update s.R ij.1 (s.R ij.1 + ∑ g, qtPush (g, ij) (r g)),
          s.Z + ∑ g, qtPush (g, ij) (c g + r g)⟩

/-- p. 17, Algorithm 3 line 4: one round of parallel decoding, the substeps on `V₀₀, V₀₁, V₁₀, V₁₁`
in this order. -/
def IsParRound (CA : Submodule (ZMod 2) (A → ZMod 2)) (CB : Submodule (ZMod 2) (B → ZMod 2))
    (s s' : SeqDecState (G × A × B)) : Prop :=
  ∃ s₁ s₂ s₃, IsParSubstep CA CB (false, false) s s₁ ∧ IsParSubstep CA CB (false, true) s₁ s₂ ∧
    IsParSubstep CA CB (true, false) s₂ s₃ ∧ IsParSubstep CA CB (true, true) s₃ s'

/-- pp. 18, 20, Algorithm 3: a run of the parallel mismatch decomposition from the mismatch `Z`;
`s k` is the state after `k` rounds (every admissible sequence of local choices is a run). -/
def IsParDecRun (CA : Submodule (ZMod 2) (A → ZMod 2)) (CB : Submodule (ZMod 2) (B → ZMod 2))
    (Z : G × A × B → ZMod 2) (s : ℕ → SeqDecState (G × A × B)) : Prop :=
  s 0 = seqDecInit Z ∧ ∀ k, IsParRound CA CB (s k) (s (k + 1))

/-! ### Decompositions, norm, active sets (§3 p. 12–13; §5 eqs. (4)–(5), p. 19) -/

/-- A quadruple `(C₀, R₀, C₁, R₁)` of vectors on the squares. -/
structure Decomp (Q : Type*) where
  /-- `C₀`, `C₁`. -/
  C : Bool → Q → ZMod 2
  /-- `R₀`, `R₁`. -/
  R : Bool → Q → ZMod 2

/-- p. 19, eq. (4) (and p. 12): `Z = C₀ + R₀ + C₁ + R₁` with every column of `C_j` a codeword of
`C_A` and every row of `R_i` a codeword of `C_B`. Columns of layer `j` are exactly the columns of
the `Q(v)`, `v ∈ V_0j`, and rows of layer `i` the rows of the `Q(v)`, `v ∈ V_i0`. -/
def IsDecomp (CA : Submodule (ZMod 2) (A → ZMod 2)) (CB : Submodule (ZMod 2) (B → ZMod 2))
    (Z : G × A × B → ZMod 2) (D : Decomp (G × A × B)) : Prop :=
  (∀ (j : Bool) (g : G), qtLocalView (D.C j) (g, (false, j)) ∈ columnCode CA B) ∧
  (∀ (i : Bool) (g : G), qtLocalView (D.R i) (g, (i, false)) ∈ rowCode A CB) ∧
  Z = D.C false + D.R false + D.C true + D.R true

/-- p. 19, eq. (5) (and p. 13): `‖C₀‖ + ‖R₀‖ + ‖C₁‖ + ‖R₁‖`, the total number of non-zero columns of
the `C_j` and non-zero rows of the `R_i`. -/
def decompNorm (D : Decomp (G × A × B)) : ℕ :=
  ∑ j : Bool, ∑ g : G, nonzeroCols (qtLocalView (D.C j) (g, (false, j))) +
  ∑ i : Bool, ∑ g : G, nonzeroRows (qtLocalView (D.R i) (g, (i, false)))

/-- p. 19: a minimum decomposition of `Z`, one whose norm (5) equals `‖Z‖`. -/
def IsMinDecomp (CA : Submodule (ZMod 2) (A → ZMod 2)) (CB : Submodule (ZMod 2) (B → ZMod 2))
    (Z : G × A × B → ZMod 2) (D : Decomp (G × A × B)) : Prop :=
  IsDecomp CA CB Z D ∧ ∀ D', IsDecomp CA CB Z D' → decompNorm D ≤ decompNorm D'

/-- p. 19 (and p. 14): the set `S_ij` of active vertices, the `v ∈ V_ij` on whose `Q(v)` the vector
`C_j + R_i` is non-zero (indexed by `g`, where `v = (g, ij)`). -/
def activeSet (D : Decomp (G × A × B)) (i j : Bool) : Finset G :=
  Finset.univ.filter fun g => qtLocalView (D.C j + D.R i) (g, (i, j)) ≠ 0

/-- p. 14, p. 21: `‖c_v‖ + ‖r_v‖` at `v ∈ V_ij`, where `c_v` and `r_v` are the restrictions of `C_j`
and `R_i` to `Q(v)`. -/
def localNorm (D : Decomp (G × A × B)) (v : G × (Bool × Bool)) : ℕ :=
  nonzeroCols (qtLocalView (D.C v.2.2) v) + nonzeroRows (qtLocalView (D.R v.2.1) v)

/-- p. 14, p. 21: the exceptional vertices `S^e_ij ⊆ S_ij`, those with `‖c_v‖ + ‖r_v‖ ≥ αΔ`. -/
noncomputable def exceptionalSet (D : Decomp (G × A × B)) (α : ℝ) (Δ : ℕ) (i j : Bool) : Finset G :=
  (activeSet D i j).filter fun g => α * Δ ≤ (localNorm D (g, (i, j)) : ℝ)

/-- p. 14, p. 21: `v` is an ordinary vertex: active (in `S_ij`) and not exceptional. -/
def IsOrdinary (D : Decomp (G × A × B)) (α : ℝ) (Δ : ℕ) (v : G × (Bool × Bool)) : Prop :=
  v.1 ∈ activeSet D v.2.1 v.2.2 ∧ (localNorm D v : ℝ) < α * Δ

/-- p. 10–11: the neighbour of `v` across the B-edge labelled `b`
(`(g, 0j) — (gb, 1j)`); `Q(v)` and `Q(bNbr v b)` share the column labelled `b`. -/
def bNbr (v : G × (Bool × Bool)) (b : G) : G × (Bool × Bool) :=
  if v.2.1 then (v.1 * b⁻¹, (false, v.2.2)) else (v.1 * b, (true, v.2.2))

/-- p. 10–11: the neighbour of `v` across the A-edge labelled `a`
(`(g, i0) — (ag, i1)`); `Q(v)` and `Q(aNbr v a)` share the row labelled `a`. -/
def aNbr (v : G × (Bool × Bool)) (a : G) : G × (Bool × Bool) :=
  if v.2.2 then (a⁻¹ * v.1, (v.2.1, false)) else (a * v.1, (v.2.1, true))

open Classical in
/-- p. 15 (before Lemma 11) and p. 23 (Lemma 16): the set `T` of vertices `v ∈ V_ij` whose
`Q(v)` contains a column `b` on which `C_j` is non-zero and which is shared with an ordinary vertex
`w ∈ V_īj` (the B-neighbour of `v` along `b`). -/
noncomputable def colShareSet (D : Decomp (G × A × B)) (α : ℝ) (Δ : ℕ) (i j : Bool) : Finset G :=
  Finset.univ.filter fun g => ∃ b : B,
    (∃ a : A, qtLocalView (D.C j) (g, (i, j)) (a, b) ≠ 0) ∧ IsOrdinary D α Δ (bNbr (g, (i, j)) (b : G))

open Classical in
/-- p. 15 (Lemma 11) and p. 23 (Lemma 16), second set: the active vertices `v ∈ S_ij` whose `Q(v)`
contains a row `a` on which `R_i` is non-zero and which is shared with an ordinary vertex
`w ∈ V_iȷ̄` (the A-neighbour of `v` along `a`). The lemmas use it with `(i, j)` replaced by `(ī, ȷ̄)`. -/
noncomputable def rowShareSet (D : Decomp (G × A × B)) (α : ℝ) (Δ : ℕ) (i j : Bool) : Finset G :=
  (activeSet D i j).filter fun g => ∃ a : A,
    (∃ b : B, qtLocalView (D.R i) (g, (i, j)) (a, b) ≠ 0) ∧ IsOrdinary D α Δ (aNbr (g, (i, j)) (a : G))

/-! ### Representations of codewords (§3, pp. 12–13) -/

/-- pp. 12–13: `D = (C₀, R₀, C₁, R₁)` is a representation of `x ∈ 𝒞₁`: `x = C₁ + R₀ = C₀ + R₁`
(so `C₀ + R₀ + C₁ + R₁ = 0`). -/
def IsRepr (CA : Submodule (ZMod 2) (A → ZMod 2)) (CB : Submodule (ZMod 2) (B → ZMod 2))
    (x : G × A × B → ZMod 2) (D : Decomp (G × A × B)) : Prop :=
  IsDecomp CA CB 0 D ∧ x = D.C true + D.R false

/-- p. 13: the vector `x⁰ := C₀ + R₀ = C₁ + R₁` attached to a representation. -/
def reprZero (D : Decomp (G × A × B)) : G × A × B → ZMod 2 :=
  D.C false + D.R false

/-- p. 13: `D` is a representation of `y` viewed as a Tanner codeword on `𝒢□₀`:
`y = C₀ + R₀ = C₁ + R₁`. -/
def IsRepr0 (CA : Submodule (ZMod 2) (A → ZMod 2)) (CB : Submodule (ZMod 2) (B → ZMod 2))
    (y : G × A × B → ZMod 2) (D : Decomp (G × A × B)) : Prop :=
  IsDecomp CA CB 0 D ∧ y = D.C false + D.R false

/-- p. 11: `𝒞₁^⊥`, the span of the `σ_z`-type generators, codewords of `C_A^⊥ ⊗ C_B^⊥` placed on the
`Q(v)`, `v ∈ V₁ = V₀₁ ∪ V₁₀` (the counterpart of the published `qtSigmaXSpan`). -/
def sigmaZSpan (CA : Submodule (ZMod 2) (A → ZMod 2)) (CB : Submodule (ZMod 2) (B → ZMod 2)) :
    Submodule (ZMod 2) (G × A × B → ZMod 2) :=
  Submodule.span (ZMod 2) {y | ∃ (v : G × (Bool × Bool)) (c : A × B → ZMod 2),
    v.2.1 ≠ v.2.2 ∧ c ∈ tensorCode (codeDual CA) (codeDual CB) ∧ y = qtPush v c}

/-! ### The sequential decoder: stalled, converging (pp. 21, 26) -/

/-- p. 21 (§5.1.1): the sequential decoder of parameter `ε` is stalled at `Z`: no vertex `v` and no
non-zero dual tensor codeword `x_v` on `Q(v)` with `|Z| − |Z + x_v| ≥ (1 − ε)|x_v|`. -/
def IsStalled (CA : Submodule (ZMod 2) (A → ZMod 2)) (CB : Submodule (ZMod 2) (B → ZMod 2))
    (ε : ℝ) (Z : G × A × B → ZMod 2) : Prop :=
  ∀ (v : G × (Bool × Bool)) (x : A × B → ZMod 2), x ∈ dualTensorCode CA CB → x ≠ 0 →
    (hammingNorm Z : ℝ) - (hammingNorm (Z + qtPush v x) : ℝ) < (1 - ε) * (hammingNorm x : ℝ)

/-- p. 26 (proof of Lemma 18): the sequential decoder of parameter `ε` converges from `s`: every
finite run of Algorithm 2 from `s` that has not reached `Ẑ = 0` can be extended by one more step. -/
def SeqConverges (CA : Submodule (ZMod 2) (A → ZMod 2)) (CB : Submodule (ZMod 2) (B → ZMod 2))
    (ε : ℝ) (s : SeqDecState (G × A × B)) : Prop :=
  ∀ (t : ℕ → SeqDecState (G × A × B)) (m : ℕ), t 0 = s →
    (∀ i < m, SeqDecStep CA CB ε (t i) (t (i + 1))) →
    (t m).Z ≠ 0 → ∃ s', SeqDecStep CA CB ε (t m) s'

/-! ### The square graphs `𝒢□₀`, `𝒢□₁` (p. 10) -/

/-- p. 10: the vertex of type `ij` of the square indexed by `(g, a, b)`, i.e. of
`{(g, 00), (ag, 01), (gb, 10), (agb, 11)}`. -/
def sqVertex (q : G × A × B) (ij : Bool × Bool) : G :=
  (if ij.2 then (q.2.1 : G) else 1) * q.1 * (if ij.1 then (q.2.2 : G) else 1)

/-- The two vertex types of `𝒢□_k`: `V₀₀, V₁₁` for `k = 0`, `V₀₁, V₁₀` for `k = 1`. -/
def sqSide (k b : Bool) : Bool × Bool :=
  if k then (b, !b) else (b, b)

/-- p. 10: the adjacency matrix of `𝒢□_k` (`k = 0`: on `V₀ = V₀₀ ∪ V₁₁`; `k = 1`: on
`V₁ = V₀₁ ∪ V₁₀`), on `G × Bool` where `(g, b)` is the vertex `(g, sqSide k b)`: one edge per square
containing both vertices (multiple edges counted). -/
def squareGraphAdj (A B : Finset G) (k : Bool) : Matrix (G × Bool) (G × Bool) ℝ :=
  Matrix.of fun u w => if u.2 ≠ w.2 then
    ((Finset.univ.filter fun q : G × A × B =>
      sqVertex q (sqSide k u.2) = u.1 ∧ sqVertex q (sqSide k w.2) = w.1).card : ℝ) else 0

end QTDecode.Parallel


