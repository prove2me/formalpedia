-- Prove2me | Definitions.Def_Holant3Dich_InC
-- name    : Holant3Dich_InC
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T04:43:42.384481+00:00
-- url     : https://prove2.me/theorems/a19acf1d-6714-4a35-ba49-ce13b7c73b19
-- title:
--   The support classes $\mathcal E$, $\mathcal C$, $ij|k$ and $\mathrm{Swap}_{\mathsf{BG};\mathsf R}$
-- statement:
--   Classes of domain-3 signatures defined by their support (not up to holographic transformation), p.19. Let $F$ have arity $n$.
--
--   1. $F\in\mathcal E$ if $\operatorname{supp}F\subseteq\{x,y,z\}$ for some $x,y,z\in\{\mathsf B,\mathsf G,\mathsf R\}^n$ with $x_i,y_i,z_i$ pairwise distinct for every $i$.
--   2. $F\in\mathcal C$ if $\operatorname{supp}F\subseteq\{\mathsf G\mathsf B^{n-1},\mathsf B\mathsf G\mathsf B^{n-2},\dots,\mathsf B^{n-1}\mathsf G\}\cup\{\mathsf B,\mathsf R\}^n$: every input with a nonzero value either contains no $\mathsf G$, or contains exactly one $\mathsf G$ and is $\mathsf B$ elsewhere.
--   3. $F$ is **domain separated** $ij|k$ if $\operatorname{supp}F\subseteq\{i,j\}^*\cup\{k\}^*$; the mission uses $\mathsf{BG}|\mathsf R$ and $\mathsf{BR}|\mathsf G$.
--   4. A binary $F$ is $\mathrm{Swap}_{\mathsf{BG};\mathsf R}$ if its matrix has the form $\begin{pmatrix}0&0&a\\0&0&b\\c&d&0\end{pmatrix}$, i.e. it vanishes unless exactly one of its two inputs is $\mathsf R$.
--
--   These classes carry the unique-propagation, counting-and-vanishing and domain-separation algorithms of §4.
--
--   **Formalization Note** `Sep k F` is the class $ij|k$ with $\{i,j\}$ the complement of $k$: `Sep 2` is $\mathsf{BG}|\mathsf R$ and `Sep 1` is $\mathsf{BR}|\mathsf G$ ($\mathsf B=0,\mathsf G=1,\mathsf R=2$).
-- source:
--   Cai, Ihm, Group Action and Spin Representation Lead to a Holant* Complexity Dichotomy on Domain Size 3, STOC 2027 submission, arXiv:2610.04750 (held manuscript sha256 b608db44…), §2.6 p.19

import Mathlib
import Definitions.Def_Holant3Dich_Sig

set_option autoImplicit false

namespace Holant3Dich

/-- The class **ℰ**: the support of `F` (arity `n`) lies in a set `{x, y, z}` of three inputs that
are pairwise different in every coordinate. Cai–Ihm, *Group Action and Spin Representation Lead to
a Holant\* Complexity Dichotomy on Domain Size 3*, STOC 2027 submission, arXiv:2610.04750 (held
manuscript sha256 b608db44…), §2.6, p.19: "Let E denote the set of domain 3 signatures F such that
if F has arity n, then supp F ⊆ {x, y, z} for some x = (x1, . . . , xn), y = (y1, . . . , yn),
z = (z1, . . . , zn) ∈ {B, G, R}^n such that for all 1 ≤ i ≤ n, xi, yi, zi are all distinct."

**Formalization Note.** A support condition, not up to holographic transformation. -/
def InE (F : Sig 3) : Prop :=
  ∃ x y z : Fin F.1 → Fin 3, (∀ i, x i ≠ y i ∧ x i ≠ z i ∧ y i ≠ z i) ∧
    ∀ w, F.2 w ≠ 0 → w = x ∨ w = y ∨ w = z

/-- The class **𝒞**: the support of `F` lies in `{GB^{n−1}, BGB^{n−2}, …, B^{n−1}G} ∪ {B, R}^n`,
i.e. every input with a nonzero value either has no `G`, or has exactly one `G` and all other
entries `B`. Cai–Ihm, §2.6, p.19: "Let C denote the set of domain 3 signatures F such that if F
has arity n, then supp F ⊆ {GB^{n−1}, BGB^{n−2}, . . . , B^{n−1}G} ∪ {B, R}^n." (B = 0, G = 1,
R = 2.) -/
def InC (F : Sig 3) : Prop :=
  ∀ x, F.2 x ≠ 0 → (∀ t, x t ≠ 1) ∨ (∃ t, x t = 1 ∧ ∀ s, s ≠ t → x s = 0)

/-- The **domain-separated** class `ij|k` with `{i, j}` the complement of `k`: `F` vanishes on every
input that uses both a value from `{i, j}` and the value `k`. `Sep 2` is `BG|R`, `Sep 1` is `BR|G`.
Cai–Ihm, §2.6, p.19: "ij|k (domain separated): F is in this class if supp F ⊆ {i, j}^∗ ∪ {k}^∗.
In other words, F is zero on inputs that take values from both {i, j} and {k}." -/
def Sep (k : Fin 3) (F : Sig 3) : Prop :=
  ∀ x, F.2 x ≠ 0 → (∀ t, x t ≠ k) ∨ (∀ t, x t = k)

/-- `F` is a **`Swap_{BG;R}`** binary signature: its matrix has the form
`[[0, 0, a], [0, 0, b], [c, d, 0]]`, i.e. it vanishes unless exactly one of its two inputs is `R`.
Cai–Ihm, §2.6, p.19: "We call a binary signature/matrix of the form [[0, 0, a], [0, 0, b],
[c, d, 0]] for some a, b, c, d ∈ C as a Swap_{BG;R} signature/matrix." -/
def IsSwapBGR (F : Sig 3) : Prop :=
  F.1 = 2 ∧ ∀ x, F.2 x ≠ 0 → (Finset.univ.filter fun t => x t = 2).card = 1

end Holant3Dich


