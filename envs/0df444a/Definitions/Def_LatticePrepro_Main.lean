-- Prove2me | Definitions.Def_LatticePrepro_Main
-- name    : LatticePrepro_Main
-- status  : Definition
-- author  : @WizardOfMenlo
-- created : 2026-11-13T15:47:01.124211+00:00
-- url     : https://prove2.me/theorems/70a63a71-befd-40a4-b78f-41b55bce3216
-- title:
--   Outputs of Theorems 4.8 and 5.1: gap reductions, fixed code and lattice gaps, and the explicit exponents
-- statement:
--   This bundle defines the objects produced by the main theorems. Throughout, $p$ is a prime and $V$ is a quadratic verifier over $\mathbb{F}_p$ with instance length $n$, $S$ assignment coordinates and language $L(V)\subseteq\{0,1\}^n$.
--
--   1. **Gap reductions** (`GapReduction p V g m`, the output of Theorem 4.8 for integers $g,m$). A linear system family $\mathcal{L}$ over $\mathbb{F}_p$ (a fixed linear map $A$, a right-hand side $b_x$ for every $x\in\{0,1\}^n$, and $N_{\mathrm{col}}$ columns partitioned into $D$ blocks of size $b$) such that
--      - $\mathcal{L}$ is a gap reduction from $L(V)$ with gap $g$: for $x\in L(V)$ the system $Av=b_x$ has a binary solution with at most one nonzero entry per block, and for $x\notin L(V)$ every solution has Hamming weight $>g\cdot D$;
--      - $g<b$, and $b=p^e$ for some $e\ge0$;
--      - $D\ge1$;
--      - $N_{\mathrm{col}}^{\,m}\le\bigl(8p^4m(S+1)\bigr)^{(m+7)m}\cdot g^{m+1}$.
--   2. **Explicit exponents.** For a real $\delta$ and natural numbers $p,m$:
--   $$m(\delta)=\Bigl\lceil\frac{\delta}{1-\delta}\Bigr\rceil+1,\qquad a(p,m)=(8p^4m+1)(m+7)m,$$
--   $$k(p,\delta)=\Bigl\lceil\frac{6m+a}{m-\delta(m+1)}\Bigr\rceil+1,\qquad C(p,\delta)=a+k\,(m+1)+2,$$
--   where in the last two formulas $m=m(\delta)$ and $a=a(p,m)$ (`momentAxes`, `prefactorExp`, `gapExp`, `sizeExp`). Theorem 5.1 uses the gap $g=(S+1)^k$ and the dimension bound $(S+1)^C$.
--   3. **Fixed code gaps** (`CodeGap F ε Lang n C`, Theorem 5.1 for codes), for a field $F$, a real $\varepsilon$, a language $\mathrm{Lang}\subseteq X$, a size parameter $\nu\in\mathbb{N}$ (the Lean argument `n`) and an exponent $C\in\mathbb{N}$. An $F$-linear code $\mathcal{C}\subseteq F^M$, a target $t_x\in F^M$ for every $x\in X$, and an integer radius $R\ge1$, with
--      - $1\le M\le \nu^C$;
--      - $x\in\mathrm{Lang}\Rightarrow\operatorname{dist}(t_x,\mathcal{C})\le R$ and $x\notin\mathrm{Lang}\Rightarrow\operatorname{dist}(t_x,\mathcal{C})>M^{1-\varepsilon}R$, where $\operatorname{dist}(y,\mathcal{C})=\min_{c\in\mathcal{C}}d_H(y,c)$ is the Hamming distance to the code.
--   4. **Fixed lattice gaps** (`LatticeGap pn ε Lang n C`, Theorem 5.1 for lattices), for a norm exponent $1\le p\le\infty$ with $s=\min\{p,2\}$, and $\mathrm{Lang},\nu,C$ as above. A lattice $\Lambda\subseteq\mathbb{Z}^M$, a target $t_x\in\mathbb{Z}^M$ for every $x$, an integer radius $R\ge1$ and an integer $N\ge1$, with
--      - $1\le M\le \nu^C$ and $N\cdot\mathbb{Z}^M\subseteq\Lambda$, so that $\Lambda$ has full rank;
--      - $x\in\mathrm{Lang}\Rightarrow\operatorname{dist}_p(t_x,\Lambda)\le R$ and $x\notin\mathrm{Lang}\Rightarrow\operatorname{dist}_p(t_x,\Lambda)>M^{1/s-\varepsilon}R$, where $\operatorname{dist}_p(t,\Lambda)=\inf_{v\in\Lambda}\|t-v\|_p$.
--
--   These structures are the conclusions of `exists_gapReduction` (Theorem 4.8) and of `code_gap`, `exists_code_gap`, `lattice_gap`, `exists_lattice_gap` (Theorem 5.1, with $\nu=S+1$). The exponents implement the parameter choice in the proof of Theorem 5.1, with $\delta=1-s\varepsilon$. The code (resp. lattice) and the radius are fixed; only the target depends on the instance.
--
--   **Formalization Note** The theorems assert `Nonempty` of these structures. The code distance `codeDist` is a natural number defined via `sInf`; the lattice distance `latticeDist` is a real infimum `⨅` (shown elsewhere to be attained). Ceilings are `Nat.ceil`; $M^{1-\varepsilon}$ and $M^{1/s-\varepsilon}$ are real powers (`Real.rpow`). A norm exponent `PNorm` is either a real $p\ge1$ or $\infty$, with $s=\min\{p,2\}$, resp. $s=2$. Polynomial-time computability is not formalized. The search test of Lemma 5.2 is not part of these structures: without its running-time bound an abstract test would be satisfied by membership in $\mathrm{Lang}$ itself, so it is stated separately for the paper's concrete tests (`CodeFamily.Accepts`, `LatticeReduction.Accepts`).
-- source:
--   G. Weissenberg, G. Fenzi, Nearly Optimal Hardness for CVP and NCP with Preprocessing (STOC 2027 submission #847), Theorem 4.8 (\label{thm:quantitative-affine-gap}) and Theorem 5.1 (\label{thm:approximation-hardness}); Lean: LatticePrepro/Main.lean, LatticePrepro.GapReduction, LatticePrepro.momentAxes, LatticePrepro.prefactorExp, LatticePrepro.gapExp, LatticePrepro.sizeExp, LatticePrepro.CodeGap, LatticePrepro.LatticeGap

import Mathlib
import Definitions.Def_LatticePrepro_Basic_Blocks
import Definitions.Def_LatticePrepro_Reduction_LinearSystem
import Definitions.Def_LatticePrepro_Conversions_Codes
import Definitions.Def_LatticePrepro_Conversions_ConstructionA
import Definitions.Def_LatticePrepro_Conversions_Hadamard
import Definitions.Def_LatticePrepro_Conversions_Lattices
import Definitions.Def_LatticePrepro_Lattices_Distance
import Definitions.Def_LatticePrepro_Lattices_Mathlib
import Definitions.Def_LatticePrepro_Moments_Basic
import Definitions.Def_LatticePrepro_Moments_Representation
import Definitions.Def_LatticePrepro_Verifier_Quadratic
import Definitions.Def_LatticePrepro_Reduction_FixedSystem
import Definitions.Def_LatticePrepro_Tables_Digits
import Definitions.Def_LatticePrepro_Tables_FieldSetup
import Definitions.Def_LatticePrepro_Tables_Hankel
import Definitions.Def_LatticePrepro_Tables_Construction
import Definitions.Def_LatticePrepro_Tables_ElementTable
import Definitions.Def_LatticePrepro_Tables_TableSoundness
import Definitions.Def_LatticePrepro_Tables_Explicit

/-!
# Main results

* **Theorem 4.8** (`GapReduction`, `exists_gapReduction`): for every prime `p`, quadratic
  verifier `V` with `S` coordinates, gap `g ≥ 1` and `m ≥ 1`, there is a linear system family
  over `𝔽_p` that is a gap reduction from the language of `V` with gap `g`, with `g < b` and
  `n^m ≤ (8 p^4 m (S+1))^{(m+7) m} · g^{m+1}` columns.
* **Theorem 5.1** (`CodeGap`, `LatticeGap`, `code_gap`, `lattice_gap`, `exists_code_gap`,
  `exists_lattice_gap`): fixed codes over any finite field, and fixed lattices in any `ℓ_p`
  norm, with polynomial dimension `M ≤ (S + 1)^C` and approximation gap `M^{1/s - ε}` measured
  by `dist(t_x, 𝒞)` and `dist_p(t_x, Λ)`. The exponent `C = sizeExp p δ` is explicit
  (`δ = 1 - s ε`).

The polynomial-time computability claims of the paper are not formalized. In particular the
search test of Lemma 5.2 is stated for the concrete tests `CodeFamily.Accepts` and
`LatticeReduction.Accepts` (`Conversions/SearchTest.lean`) rather than as a field of `CodeGap` and
`LatticeGap`: without its running-time bound, an abstract "test" field would be satisfiable by
the membership predicate of `Lang` itself.
-/

namespace LatticePrepro

/-! ### Restricting an encoding tuple to fewer coordinates -/

/-! ### Theorem 4.8 -/

/-- The output of Theorem 4.8 for a verifier `V`, a gap `g` and `m ≥ 1`: a linear system family
`L` over `𝔽_p` that is a gap reduction from `L(V)` with gap `g < b` (`b` a power of `p`), with at
least one block and `n^m ≤ (8 p^4 m (S + 1))^{(m+7) m} · g^{m+1}` columns. -/
structure GapReduction (p : ℕ) [Fact p.Prime] (V : QuadraticVerifier p) (g m : ℕ) where
  /-- The fixed linear system. -/
  L : LinearSystemFamily (ZMod p) (Fin V.n → Bool)
  isGapReduction : L.IsGapReduction V.Language g
  lt_blockSize : g < L.blockSize
  blockSize_eq_pow : ∃ e : ℕ, L.blockSize = p ^ e
  numBlocks_pos : 0 < L.numBlocks
  card_pow_le : (Fintype.card L.ι) ^ m ≤ (8 * p ^ 4 * m * (V.S + 1)) ^ ((m + 7) * m) * g ^ (m + 1)

/-! ### Choice of parameters for Theorem 5.1

For a gap exponent `0 ≤ δ < 1` we choose `m` with `δ (1 + 1/m) < 1`, then the gap `g = (S+1)^k`
with `k` large enough that `64 · n^δ ≤ g`, and the size exponent `C` with `4 n ≤ (S+1)^C`, where
`n^m ≤ (8 p^4 m (S+1))^{(m+7) m} g^{m+1}` is the column bound of Theorem 4.8. All three
constants are explicit functions of `p` and `δ`. -/

/-- The number of moment axes `m = ⌈δ / (1 - δ)⌉ + 1`, so that `δ (m + 1) < m`. -/
noncomputable def momentAxes (δ : ℝ) : ℕ := ⌈δ / (1 - δ)⌉₊ + 1

/-- The exponent `a = (8 p^4 m + 1) (m + 7) m`, with `(8 p^4 m (S+1))^{(m+7) m} ≤ (S+1)^a`. -/
def prefactorExp (p m : ℕ) : ℕ := (8 * p ^ 4 * m + 1) * ((m + 7) * m)

/-- The gap exponent `k`, giving the gap `g = (S+1)^k`. -/
noncomputable def gapExp (p : ℕ) (δ : ℝ) : ℕ :=
  ⌈(6 * momentAxes δ + prefactorExp p (momentAxes δ) : ℝ) /
    (momentAxes δ - δ * (momentAxes δ + 1))⌉₊ + 1

/-- The size exponent `C`, giving `M ≤ (S+1)^C`. -/
noncomputable def sizeExp (p : ℕ) (δ : ℝ) : ℕ :=
  prefactorExp p (momentAxes δ) + gapExp p δ * (momentAxes δ + 1) + 2

/-! ### Theorem 5.1 for codes -/

/-- A fixed code with gap `M^{1 - ε}` for a language `Lang ⊆ X` with size parameter `n` and
exponent `C` (the conclusion of Theorem 5.1 for codes): a code `𝒞 ⊆ F^M` with `1 ≤ M ≤ n^C`,
targets `t_x` and an integer radius `R ≥ 1` such that `x ∈ Lang` implies `dist(t_x, 𝒞) ≤ R` and
`x ∉ Lang` implies `dist(t_x, 𝒞) > M^{1 - ε} · R`. -/
structure CodeGap (F : Type) [Field F] [DecidableEq F] (ε : ℝ) {X : Type} (Lang : Set X)
    (n C : ℕ) where
  /-- The fixed code and the targets. -/
  𝒞 : CodeFamily F X
  /-- The radius. -/
  R : ℕ
  one_le_R : 1 ≤ R
  one_le_card : 1 ≤ Fintype.card 𝒞.M
  card_le : Fintype.card 𝒞.M ≤ n ^ C
  yes : ∀ x ∈ Lang, CodeFamily.codeDist (𝒞.target x) 𝒞.code ≤ R
  no : ∀ x ∉ Lang,
    (Fintype.card 𝒞.M : ℝ) ^ (1 - ε) * R < CodeFamily.codeDist (𝒞.target x) 𝒞.code

/-! ### Theorem 5.1 for lattices -/

/-- A fixed lattice with gap `M^{1/s - ε}` in `ℓ_p` for a language `Lang ⊆ X` with size
parameter `n` and exponent `C` (the conclusion of Theorem 5.1 for lattices): a full-rank lattice
`Λ ⊆ ℤ^M` (containing `N · ℤ^M`) with `1 ≤ M ≤ n^C`, integer targets `t_x` and an integer radius
`R ≥ 1` such that `x ∈ Lang` implies `dist_p(t_x, Λ) ≤ R` and `x ∉ Lang` implies
`dist_p(t_x, Λ) > M^{1/s - ε} · R`. -/
structure LatticeGap (pn : PNorm) (ε : ℝ) {X : Type} (Lang : Set X) (n C : ℕ) where
  /-- The fixed lattice and the targets. -/
  Λ : LatticeFamily X
  /-- The radius. -/
  R : ℕ
  one_le_R : 1 ≤ R
  one_le_card : 1 ≤ Fintype.card Λ.M
  card_le : Fintype.card Λ.M ≤ n ^ C
  /-- The lattice contains `N · ℤ^M`. -/
  N : ℕ
  N_pos : 0 < N
  smul_mem : ∀ v : Λ.M → ℤ, (N : ℤ) • v ∈ Λ.lattice
  yes : ∀ x ∈ Lang, Λ.latticeDist pn x ≤ R
  no : ∀ x ∉ Lang, (Fintype.card Λ.M : ℝ) ^ (1 / pn.s - ε) * R < Λ.latticeDist pn x

end LatticePrepro


