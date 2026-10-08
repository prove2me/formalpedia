-- Prove2me | Definitions.Def_ErschlerZheng_Grigorchuk
-- name    : ErschlerZheng_Grigorchuk
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-05T21:24:52.154693+00:00
-- url     : https://prove2.me/theorems/eee6161c-3032-4b7e-aa2b-6f3e4ab84832
-- title:
--   Erschler–Zheng §§2.3–2.5, 3, 7.1, 8 — the binary tree and its rays, the groups G_ω, the substitutions ζ_i, germs, Assumption Fr(D), the Schreier distance and Gray code, L^ω_n, λ_0 and α_0
-- statement:
--   Definitions from Erschler and Zheng, *Growth of periodic Grigorchuk groups*, Invent. Math. 219 (2020) 1069–1155, https://doi.org/10.1007/s00222-019-00922-0 (page numbers of arXiv:1802.09077v2), built on the published Garrido bundle (`Garrido.BinaryTreeAut`, the automorphisms of the rooted binary tree as permutations of the finite words `List Bool` preserving length and the prefix order; `Garrido.grigA`, the automorphism $a$ that changes the first letter) and on the Germs and Walks bundles. Digits: `false` is $0$ and `true` is $1$. Strings $\omega = \omega_0\omega_1\ldots$ are functions `ℕ → Fin 3`, indexed from $0$; the digits $x_1 x_2 \ldots$ of vertices and rays are Lean's indices $0, 1, \ldots$, which p. 35 warns about: “To avoid possible confusion about indexing, keep in mind that the string $\omega \in \{\mathbf 0, \mathbf 1, \mathbf 2\}^\infty$ starts with $\omega_0$, $\omega = \omega_0\omega_1\ldots$ while tree vertices are recorded as $v = v_1 v_2 \ldots$.”
--
--   **The tree, its rays and the right action.**
--   - `vertexRightAction` and `rayRightAction`: the right action $v \cdot g$ of p. 9 (“We consider right group actions $\Gamma \curvearrowright X$ and write the action of group element $g$ on $x \in X$ as $x \cdot g$.”), defined as $g^{-1}(v)$ on Garrido's left model, so that $v \cdot (gh) = (v \cdot g) \cdot h$ and the groups are Garrido's subgroups unchanged. `Ray` is the boundary $\partial \mathsf T$, the functions `ℕ → Bool` (p. 13: “The boundary $\partial \mathsf T_{\mathbf d}$ of the tree $\mathsf T_{\mathbf d}$ is the set of infinite rays $x = v_1 v_2 \ldots$ with $v_j \in \{0, 1, \ldots, d_j - 1\}$ for each $j \in \mathbb N$.”), with the product topology; digit $i$ of $x \cdot g$ is digit $i$ of $(x_1 \ldots x_{i+1}) \cdot g$, and each map $x \mapsto x \cdot g$ is continuous (`rayContinuousConstSMul`), as p. 18 says: “Let $G < \mathrm{Aut}(\mathsf T_{\mathbf d})$, then $G$ acts on the boundary of the tree $\mathcal X = \partial \mathsf T_{\mathbf d}$ by homeomorphisms.” `rayPrefix x n` is $x_1 \ldots x_n$.
--   - `oneRay` is $o = 1^\infty$; `IsCofinal x` says that all but finitely many digits of $x$ are $1$, “cofinal with $1^\infty$” (p. 18); `prepend u x` is the ray $ux$ and `commonPrefixLength u x` is $|u \wedge x|$, after p. 9: “On a regular rooted tree $\mathsf T$, given a vertex $u \in \mathsf T$ and $v \in \mathsf T \cup \partial \mathsf T$, $uv$ denotes the concatenation of the strings, that is the ray with prefix $u$ followed by $v$. Given $u, v \in \mathsf T \cup \partial \mathsf T$, $u \wedge v$ denotes the longest common prefix of $u$ and $v$.” `shiftRay x n` is $\mathfrak s^n x = x_{n+1} x_{n+2} \ldots$ (Fact 7.4, p. 35: “Denote by $\mathfrak s$ the shift on strings.”).
--
--   **Sections, stabilizers, $\iota$, finitary automorphisms (pp. 13–14, 18).**
--   - `sec g v` is the section $g_v$ of p. 13 (“Apply the wreath recursion $n$ times, we have $\psi^n : \mathrm{Aut}(\mathsf T_d) \to \mathrm{Aut}(\mathsf T_{\mathfrak s^n\mathbf d}) \wr_{\mathsf L_n} \mathrm{Aut}(\mathsf T^n_{\mathbf d})$, $g \mapsto (g_v)_{v \in \mathsf L_n} \tau_n(g)$, where finitary permutation $\tau_n(g)$ is the projection of $g$ to the automorphism group of the finite tree $\mathsf T^n_{\mathbf d}$, and $g_v$ is called the *section* of $g$ at vertex $v$.”) for the right action: the automorphism with $(vy) \cdot g = (v \cdot g)(y \cdot g_v)$ for every word $y$, which is how Lemma 7.5's proof (p. 35) reads it: “$x \cdot g = (v \cdot \tau)x' \cdot g_v$”. It is Garrido's `treeSection` of $g^{-1}$ at $v$, inverted.
--   - `levelStab K n` and `rist K u` are p. 13: “The $n$-th level stabilizer $\mathrm{St}_G(\mathsf L_n)$ consists of the automorphisms in $G$ that fix all the vertices on level $n$” and “The rigid vertex stabilizer of $u$ in $G$, denoted by $\mathrm{Rist}_G(u)$, consists of the automorphisms in $G$ that fix all vertices not having $u$ as a prefix.”
--   - `iota h u` is $\iota(h, u)$ of (2.1), p. 14: “The group of automorphisms of the subtree rooted at $u$ is embedded in $\mathrm{Aut}(\mathsf T_d)$ as rigid vertex stabilizer of $u$ by (2.1) $\iota(\cdot : u) : \mathrm{Aut}(\mathsf T^u_{\mathfrak s^n\mathbf d}) \to \mathrm{Aut}(\mathsf T_{\mathfrak s^n\mathbf d}) \wr_{\mathsf L_n} \mathrm{Aut}(\mathsf T^n_{\mathbf d}) \quad h \mapsto (g_v)$, where $g_u = h$ and $g_v = e$ for any $v \neq u$.” It acts as $h$ below $u$, $(uy) \cdot \iota(h, u) = u(y \cdot h)$, and trivially elsewhere.
--   - `finitary` is the group $L$ of p. 18: “Let $L$ be the subgroup of $\mathrm{Aut}(\mathsf T_{\mathbf d})$ that consists of all finitary automorphisms. In other words, an element $g \in \mathrm{Aut}(\mathsf T_{\mathbf d})$ is in $L$ if there exists a finite level $n$ such that all sections $g_v$ for $v \in \mathsf L_n$ are trivial.”
--
--   **The groups $G_\omega$ (§2.4, p. 14).**
--   - `BCD`, `BCD.killedBy` and `letterValue`: “Let $\{\mathbf 0, \mathbf 1, \mathbf 2\}$ be the three non-trivial homomorphisms from the 4-group $(\mathbb Z/2\mathbb Z) \times (\mathbb Z/2\mathbb Z) = \{id, b, c, d\}$ to the 2-group $\mathbb Z/2\mathbb Z = \{id, a\}$. They are ordered in such a way that $\mathbf 0, \mathbf 1, \mathbf 2$ vanish on $d, c, b$ respectively.” `killedBy i` is the letter on which $i$ vanishes ($0 \mapsto d$, $1 \mapsto c$, $2 \mapsto b$), and `letterValue i γ` is `true` when $i(\gamma) = a$.
--   - $\Omega$ is the type `ℕ → Fin 3` and `shiftSeq ω k` is $\mathfrak s^k \omega = \omega_k \omega_{k+1} \ldots$, after p. 14: “Let $\Omega = \{\mathbf 0, \mathbf 1, \mathbf 2\}^\infty$ be the space of infinite sequences over letters $\{\mathbf 0, \mathbf 1, \mathbf 2\}$. The space $\Omega$ is endowed with the shift map $\mathfrak s : \Omega \to \Omega$, $\mathfrak s(\omega_0\omega_1 \ldots) = \omega_1\omega_2 \ldots$.”
--   - `gen ω γ` is $\gamma_\omega$ for $\gamma \in \{b, c, d\}$, after “Given an $\omega \in \Omega$, the Grigorchuk group $G_\omega$ acting on the rooted binary tree is generated by $\{a, b_\omega, c_\omega, d_\omega\}$, where $a = (id, id)\varepsilon$, $\varepsilon$ transposes 0 and 1, and the automorphisms $b_\omega, c_\omega, d_\omega$ are defined recursively according to $\omega$ as follows. The wreath recursion sends $\psi_n : G_{\mathfrak s^n\omega} \to G_{\mathfrak s^{n+1}\omega} \wr_{\{0,1\}} \mathfrak S_2$ by $\psi_n(b_{\mathfrak s^n\omega}) = (\omega_n(b), b_{\mathfrak s^{n+1}\omega})$, $\psi_n(c_{\mathfrak s^n\omega}) = (\omega_n(c), c_{\mathfrak s^{n+1}\omega})$, $\psi_n(d_{\mathfrak s^n\omega}) = (\omega_n(d), d_{\mathfrak s^{n+1}\omega})$.” On the subtree of $0$ it acts as $a$ or trivially according to $\omega_0(\gamma)$, and on the subtree of $1$ as $\gamma_{\mathfrak s\omega}$; each is an involution. `gens ω` is $S = \{a, b_\omega, c_\omega, d_\omega\}$, `grigorchuk ω` is $G_\omega$, the subgroup of `Garrido.BinaryTreeAut` it generates, and `genSet ω` is $S$ as a subset of $G_\omega$. The string $\omega$ is arbitrary; for one that is eventually equal to a letter $i$, the generator on which $i$ vanishes has a trivial germ at $1^\infty$ and the other two have the same germ there (`ErschlerZheng.isLevelTransitive_and_isotropy_grigorchuk`).
--   - `firstString` is $(\mathbf{012})^\infty$, $\omega_n = n \bmod 3$: “The *first Grigorchuk group* corresponds to the periodic sequence $\omega = (\mathbf{012})^\infty$ and is often denoted as $G_{012}$.”
--
--   **Words and the substitutions (§2.4, p. 15).**
--   - `Gen4` and `evalWord ω k w`: words over $\{a, b, c, d\}$, and the product in $G_{\mathfrak s^k \omega}$ of the letters in the order written, with $b, c, d$ read as $b_{\mathfrak s^k\omega}, c_{\mathfrak s^k\omega}, d_{\mathfrak s^k\omega}$.
--   - `APair`, `APair.toWord`, `zetaPair` and `zetaWord` are (2.2): “Define self-substitutions $\zeta_i$, $i \in \{\mathbf 0, \mathbf 1, \mathbf 2\}$, of $\{ab, ac, ad\}$ by (2.2) $\zeta_{\mathbf 0} : ab \mapsto abab,\ ac \mapsto acac,\ ad \mapsto abadac$, $\zeta_{\mathbf 1} : ab \mapsto abab,\ ac \mapsto adacab,\ ad \mapsto adad$, $\zeta_{\mathbf 2} : ab \mapsto acabad,\ ac \mapsto acac,\ ad \mapsto adad$. It is understood that $\zeta_{\omega_n}$ sends $\{ab_{\mathfrak s^{n+1}\omega}, ac_{\mathfrak s^{n+1}\omega}, ad_{\mathfrak s^{n+1}\omega}\}^*$ to $\{ab_{\mathfrak s^n\omega}, ac_{\mathfrak s^n\omega}, ad_{\mathfrak s^n\omega}\}^*$ by the rules specified above”. Words over $\{ab, ac, ad\}$ are lists of the three letters of `APair`, spelled out over $\{a, b, c, d\}$ by `toWord`; the level at which $b, c, d$ are read is the argument of `evalWord`.
--   - `evalFree ω k` and `zetaFree i` extend these to the free group on $\{ab, ac, ad\}$, so that words may also use the inverses $ba, ca, da$.
--   - `zetaHat ω n g` is $\zeta_{\omega_n}$ applied to a group element, p. 15: “It follows from (2.3) that if $g \in G_{\mathfrak s^{n+1}\omega}$ can be represented by a word in $\{ab_{\mathfrak s^{n+1}\omega}, ac_{\mathfrak s^{n+1}\omega}, ad_{\mathfrak s^{n+1}\omega}\}$, then the substitution $\zeta_{\omega_n}$ can be applied to $g$ and the resulting image in $G_{\mathfrak s^n\omega}$ does not depend on the choice of the representing word.” For $g$ in the image of `evalFree ω (n + 1)` it is the value at level $n$ of $\zeta_{\omega_n}$ of a chosen preimage, and $1$ for any other $g$. Independence of the choice is the milestone `ErschlerZheng.evalFree_zetaFree_congr_and_zetaHat_evalFree_eq_of_tail_ne`, under a hypothesis on the tail of $\omega$.
--
--   **The matrices, $L^\omega_n$ and the constants (pp. 2, 28, 56–57).**
--   - `substMatrix i` is $M_i$ of p. 56: “Let $M_i$ be the matrix associated with the substitution $\zeta_i$, $i \in \{\mathbf 0, \mathbf 1, \mathbf 2\}$, such that $\mathbf l(\zeta_i(\omega)) = M_i \mathbf l(\omega)$ where $\mathbf l(\omega)$ is the column vector that records occurrence of $ab, ac, ad$ in $\omega$.” (Here $\omega$ is a word.) The entries are the printed ones, rows as printed, in the coordinates $(ab, ac, ad)$.
--   - `lengthL ω n` is (8.1), p. 57: “Define the number $L^\omega_n$ to be (8.1) $L^\omega_n := (1\ \ 1\ \ 1)\, M_{\omega_0} \ldots M_{\omega_{n-1}}\, (1\ \ 1\ \ 1)^{T}$”, where the last factor is printed as a column vector; so $L^\omega_0 = 3$.
--   - `matrixM` is the matrix $M$ of the substitution $\zeta$ of $G_{012}$ (p. 28), with rows $(1, 2, 0)$, $(1, 0, 2)$, $(1, 0, 0)$.
--   - `lambda0` and `alpha0` are p. 2: “where $\alpha_0 = \frac{\log 2}{\log \lambda_0} \approx 0.7674$, where $\lambda_0$ is the positive root of the polynomial $X^3 - X^2 - 2X - 4$.” `lambda0` is the supremum of the positive real roots of $X^3 - X^2 - 2X - 4$ ($0$ if there were none); that there is exactly one is the milestone `ErschlerZheng.existsUnique_pos_root_and_alpha0_approx_and_charpoly_matrixM`.
--
--   **Assumption Fr(D) (Notation 7.1, p. 34).**
--   - `SatisfiesFr D ω`, `frM D ω k` and `frI D ω`: “We say the string $\omega$ satisfies Assumption $(\mathrm{Fr}(D))$, where $D \in \mathbb N$, if for every integer $k \geqslant 0$, the string $\omega_{kD} \ldots \omega_{kD+D-1}$ contains at least one of the following two substring: $\{\mathbf{201}, \mathbf{211}\}$.” and “Given a string $\omega$ that satisfies Assumption $(\mathrm{Fr}(D))$, define $(m_k)_{k=0}^\infty$ and $I_\omega$ as follows: for each $k$ let $m_k$ be the smallest number in $\{0, \ldots, D-3\}$ such that $\omega_{kD+m_k}\omega_{kD+m_k+1}\omega_{kD+m_k+2} \in \{\mathbf{201}, \mathbf{211}\}$; let $I_\omega$ be the set $I_\omega := \{kD + m_k + 3 : k \geqslant 0\}$.” `SatisfiesFr D ω` asks, for every $k$, for some $m$ with $m + 3 \le D$ such that $\omega_{kD+m}\omega_{kD+m+1}\omega_{kD+m+2}$ is $\mathbf{201}$ or $\mathbf{211}$; `frM` is the least such $m$ and `frI` is $I_\omega$; both are defined for every $\omega$ (`frM` is $0$ when there is no such $m$), and the statements that use them assume `SatisfiesFr D ω`.
--
--   **The Schreier graph of $1^\infty$ and the Gray code (§7.1, pp. 34–35).**
--   - `schreierDist ω x y` is $d_{\mathcal S_\omega}(x, y)$, after p. 34: “Let $o = 1^\infty \in \partial \mathsf T$ and denote by $\mathcal S_\omega$ its *Schreier graph* under the action of $G_\omega$: the vertex set of $\mathcal S_\omega$ is $o \cdot G_\omega$ and two vertices $x, y \in o \cdot G_\omega$ are connected by an edge labelled with $s \in \{a, b_\omega, c_\omega, d_\omega\}$ if $y = x \cdot s$.” and “Let $d_{\mathcal S_\omega}$ denote the graph distance on the Schreier graph $\mathcal S_\omega$.” It is the least $n$ such that $y = x \cdot g$ for a product $g$ of at most $n$ elements of $S \cup S^{-1}$: the graph distance of p. 34, with edges crossed in either direction. It is defined for all rays and is $0$ when $y$ is not in the orbit of $x$ (a junk value). `orbitOne ω` is $1^\infty \cdot G_\omega$ and `orbitDist ω` is $d_{\mathcal S}$ as a real function on it.
--   - `maxZeroIndex x` is $n(x)$ of Fact 7.3, p. 35: “Let $x \in \partial \mathsf T$ be a point that is cofinal with $1^\infty$. Let $n(x) = \max\{k : x_k = 0\}$.” The index $k$ is the paper's, starting at $1$. It is defined for every ray, with value $0$ when $x$ has no zero or infinitely many, and the statement that uses it assumes $x$ cofinal with $1^\infty$ and $x \neq 1^\infty$.
--   - `grayList` and `grayCode x` are the Gray code of p. 34 with the printed prefix sums corrected to suffix sums. Printed: “Explicitly, for $x = x_1x_2 \ldots \in \partial \mathsf T$, flip all digits of $x$ to the ray $\check x_1\check x_2 \ldots$ where $\check x_i = 1 - x_i$. The Grey code of $x$ is $\bar x = \bar x_1 \bar x_2 \ldots$ where $\bar x_i = \check x_1 + \ldots + \check x_i \mod 2$. Note that for $x$ cofinal with $1^\infty$, its Gray code $\bar x$ has only finitely many 1’s” and “We regard such an $\bar x$ as an element in $\{0\} \cup \mathbb N$ represented by a binary string.” With prefix sums a ray cofinal with $1^\infty$ can have infinitely many 1's, against the sentence beginning “Note that” (`ErschlerZheng.isCofinal_and_printed_gray_ones_infinite_prepend_false_oneRay`). The bundle uses $\bar x_i = \check x_i + \check x_{i+1} + \cdots \bmod 2$, read as a binary number with $\bar x_1$ the least significant digit, with which Fact 7.3 holds as printed (`ErschlerZheng.schreierDist_eq_abs_sub_grayCode_of_isCofinal`). `grayCode x` is that number computed from $x_1 \ldots x_{n(x)}$, so it is $0$ for $1^\infty$ and for a ray that is not cofinal with $1^\infty$; the statement that uses it assumes both rays cofinal with $1^\infty$.
--
--   **Germs of $G_\omega$ (Example 3.2, p. 18).**
--   - `HasGermAt ω γ g x` is “$g$ has $\gamma$-germ at $x$” from “In this case a group element $g$ has $\gamma$-germ at $x$, where $\gamma \in \{b, c, d\}$, if there is a finite level $n$ such that the section of $g$ at $x_1 \ldots x_n$ is $\gamma_{\mathfrak s^n\omega}$.” It asks for a level $n$ with $x = x_1 \ldots x_n 1^\infty$ and section $\gamma_{\mathfrak s^n\omega}$ at $x_1 \ldots x_n$. The extra condition, automatic at $x = 1^\infty$, makes the $\gamma$-germ at $x$ the germ of $\gamma_{\mathfrak s^n\omega}$ at $1^\infty$ carried to $x$. Without it, $d_\omega$ would have a $d$-germ at $01^\infty$ whenever $\omega_0 = \mathbf 0$, although its germ there is trivial (`ErschlerZheng.sec_gen_nil_and_cons_false_smul_and_germ_eq_one_and_hasGermAt_iff_of_eq_zero`).
--   - `germLetterSubgroup ω γ` is $\langle \gamma \rangle$, the subgroup of the germ group at $1^\infty$ generated by the germ of $\gamma_\omega$, and `letterGerms ω γ` is $\mathcal H(\langle \gamma \rangle)$ of (3.1) for $G_\omega$ with the finitary automorphisms as auxiliary group and $o = 1^\infty$: “When $\omega$ is not eventually constant, the subgroup $\langle b \rangle = \{id, b\}$ is a proper subgroup of $\hat{\mathcal G}_o$. We refer to the corresponding sub-groupoid $\mathcal H^b = \mathcal H(\langle b \rangle)$ of $\mathcal G$ as the groupoid of $\langle b \rangle$-germs. The groupoid of $\langle c \rangle$-germs ($\langle d \rangle$-germs resp.) is defined in the same way from the subgroup $\{id, c\}$ ($\{id, d\}$ resp.) of $\hat{\mathcal G}_o$.”
--
--   **Spherically symmetric rooted trees (p. 13), for Lemma 5.6.**
--   - `SphericalVertex d`, `SphericalTreeAut d`, `SphericalRay d` and `sphericalOneRay d hd`, after “Let $\mathbf d = (d_j)_{j \in \mathbb N}$ be a sequence of integers, $d_j \geqslant 2$ for all $j \in \mathbb N$. The spherically symmetric rooted tree $\mathsf T_{\mathbf d}$ is the tree with vertices $v = v_1 \ldots v_n$ with each $v_j \in \{0, 1, \ldots, d_j - 1\}$.” Lean's `d i` is the paper's $d_{i+1}$. `SphericalTreeAut d` is $\mathrm{Aut}(\mathsf T_{\mathbf d})$ (“The group of automorphisms $\mathrm{Aut}(\mathsf T_{\mathbf d})$ of the rooted tree is the group of tree automorphisms that fix the root $\emptyset$.”) as the permutations of the vertices preserving length and the prefix order, acting on vertices and rays on the right; the condition $d_j \ge 2$ is a hypothesis only of `sphericalOneRay`, the ray $1^\infty$.
--   - `sphericalSec g v` is the section $g_v \in \mathrm{Aut}(\mathsf T_{\mathfrak s^{|v|}\mathbf d})$, with $(vy) \cdot g = (v \cdot g)(y \cdot g_v)$, and `rootPerm g` is the root permutation (“We refer to $\tau_1(g)$ as the *root permutation* of $g$”, p. 13) as the map $j \mapsto$ the digit of $j \cdot g$. Only the absence of fixed points is ever used, and $g$ and $g^{-1}$ have the same fixed points (Mathlib's `MulAction.fixedBy_inv`).
--   - `binaryVertexEquiv`, `binaryRayEquiv` and `binaryToSpherical` identify the binary tree with $\mathsf T_{\mathbf d}$ for $\mathbf d \equiv 2$.
-- source:
--   Erschler, A. and Zheng, T., Growth of periodic Grigorchuk groups, Invent. Math. 219 (2020) 1069–1155, https://doi.org/10.1007/s00222-019-00922-0 (arXiv:1802.09077v2, whose page numbers are used), pp. 9, 13–16, 27, 34–35, 56–58, §2.3–2.5, §5, §7.1, §8 (the tree, G_ω, substitutions, Fr(D), the Schreier graph, L^ω_n)

import Definitions.Def_Garrido_Grigorchuk
import Definitions.Def_ErschlerZheng_Germs

/-!
# Grigorchuk groups `G_ω`

A. Erschler and T. Zheng, *Growth of periodic Grigorchuk groups*, arXiv:1802.09077v2 (page numbers
of arXiv v2): the right action `v·g` of tree automorphisms on vertices and rays (p. 9), sections,
level and rigid stabilizers, `ι(h, u)` (§2.3, pp. 13–14), the finitary automorphisms (p. 18), the
groups `G_ω` and the substitutions `ζ_i` (§2.4, pp. 14–15), germs of `G_ω` (Example 3.2, p. 18),
Assumption `Fr(D)`, the Schreier distance and the Gray code (§7.1, pp. 34–35), the matrices `M_i`,
`L^ω_n` and the constants `λ_0`, `α_0` (pp. 2, 28, 56–57), and the spherically symmetric rooted
trees `T_d` (p. 13).

Conventions. Tree automorphisms are `Garrido.BinaryTreeAut` (permutations of finite words);
`v <• g` is `g⁻¹ v`. Digits: `false` = 0, `true` = 1. Strings `ω : ℕ → Fin 3` are indexed from 0,
`ω = ω_0 ω_1 …`; the digits `x_1 x_2 …` of vertices and rays are Lean's indices `0, 1, …`.
-/

namespace ErschlerZheng
open scoped RightActions
open Garrido

/-! ### The right action on vertices and rays -/

/-- p. 9: the right action `v·g` of a tree automorphism `g` on vertices (finite words), given by
`op g • v := g⁻¹ v`, so that `v·(gh) = (v·g)·h`. -/
instance vertexRightAction : MulAction BinaryTreeAutᵐᵒᵖ (List Bool) where
  smul g v := ((g.unop⁻¹ : BinaryTreeAut) : Equiv.Perm (List Bool)) v
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

theorem vertex_smul_def (g : BinaryTreeAut) (v : List Bool) :
    v <• g = ((g⁻¹ : BinaryTreeAut) : Equiv.Perm (List Bool)) v := rfl

theorem vertex_smul_mul (g h : BinaryTreeAut) (v : List Bool) : v <• (g * h) = (v <• g) <• h := by
  rw [MulOpposite.op_mul, mul_smul]

theorem vertex_smul_smul_inv (g : BinaryTreeAut) (v : List Bool) : v <• g <• g⁻¹ = v := by
  rw [← vertex_smul_mul, mul_inv_cancel]; exact one_smul _ v

theorem vertex_smul_inv_smul (g : BinaryTreeAut) (v : List Bool) : v <• g⁻¹ <• g = v := by
  rw [← vertex_smul_mul, inv_mul_cancel]; exact one_smul _ v

theorem length_vertex_smul (g : BinaryTreeAut) (v : List Bool) : (v <• g).length = v.length :=
  (g⁻¹).2.1 v

theorem vertex_smul_prefix_iff (g : BinaryTreeAut) (v w : List Bool) :
    v <• g <+: w <• g ↔ v <+: w :=
  ((g⁻¹).2.2 v w).symm

/-- p. 13: `∂T`, the rays `x = x₁x₂…` of the binary tree, as functions `ℕ → Bool` (`false` = 0,
`true` = 1); Lean's digit `x i` is the paper's `x_{i+1}`. -/
abbrev Ray : Type := ℕ → Bool

/-- `x₁ … xₙ`, the prefix of length `n` of a ray (Lean's digits `x 0, …, x (n - 1)`). -/
def rayPrefix (x : Ray) (n : ℕ) : List Bool := List.ofFn fun i : Fin n => x i

theorem length_rayPrefix (x : Ray) (n : ℕ) : (rayPrefix x n).length = n := by
  simp [rayPrefix]

theorem getElem_rayPrefix (x : Ray) (n i : ℕ) (h : i < (rayPrefix x n).length) :
    (rayPrefix x n)[i] = x i := by
  simp [rayPrefix]

theorem rayPrefix_prefix (x : Ray) {m n : ℕ} (h : m ≤ n) : rayPrefix x m <+: rayPrefix x n := by
  rw [List.prefix_iff_eq_take]
  apply List.ext_getElem
  · simp [length_rayPrefix, h]
  · intro i h1 h2
    simp [getElem_rayPrefix]

/-- The action on rays underlying `rayRightAction`: digit `i` of `x·g` is digit `i` of
`(x₁ … x_{i+1})·g`. -/
instance raySMul : SMul BinaryTreeAutᵐᵒᵖ Ray :=
  ⟨fun g x i => (g • rayPrefix x (i + 1)).getD i false⟩

theorem rayPrefix_smul_aux (g : BinaryTreeAutᵐᵒᵖ) (x : Ray) (n : ℕ) :
    rayPrefix (g • x) n = g • rayPrefix x n := by
  have hlen : ∀ v : List Bool, (g • v).length = v.length := fun v => length_vertex_smul g.unop v
  apply List.ext_getElem
  · simp [length_rayPrefix, hlen]
  · intro i h1 h2
    rw [getElem_rayPrefix]
    show (g • rayPrefix x (i + 1)).getD i false = _
    have hi : i < (g • rayPrefix x (i + 1)).length := by simp [hlen, length_rayPrefix]
    have hp : g • rayPrefix x (i + 1) <+: g • rayPrefix x n := by
      have := (vertex_smul_prefix_iff g.unop (rayPrefix x (i + 1)) (rayPrefix x n)).2
        (rayPrefix_prefix x (by simp [length_rayPrefix] at h1; omega))
      exact this
    rw [List.getD_eq_getElem _ _ hi]
    exact hp.getElem hi

/-- The induced right action on rays: digit `i` of `x·g` is digit `i` of `(x₁ … x_{i+1})·g`. -/
instance rayRightAction : MulAction BinaryTreeAutᵐᵒᵖ Ray :=
  { (inferInstance : SMul BinaryTreeAutᵐᵒᵖ Ray) with
    one_smul := fun x => by
      funext i
      show (rayPrefix x (i + 1)).getD i false = x i
      rw [List.getD_eq_getElem _ _ (by simp [length_rayPrefix]), getElem_rayPrefix]
    mul_smul := fun g h x => by
      funext i
      show ((g * h) • rayPrefix x (i + 1)).getD i false = (g • rayPrefix (h • x) (i + 1)).getD i false
      rw [rayPrefix_smul_aux, mul_smul] }

theorem rayPrefix_smul (g : BinaryTreeAut) (x : Ray) (n : ℕ) :
    rayPrefix (x <• g) n = rayPrefix x n <• g :=
  rayPrefix_smul_aux _ x n

/-- Each map `x ↦ x·g` on rays is continuous for the product topology on `ℕ → Bool`. -/
instance rayContinuousConstSMul : ContinuousConstSMul BinaryTreeAutᵐᵒᵖ Ray where
  continuous_const_smul g := by
    apply continuous_pi
    intro i
    change Continuous fun x : Ray => (g • rayPrefix x (i + 1)).getD i false
    have : (fun x : Ray => (g • rayPrefix x (i + 1)).getD i false) =
        (fun f : Fin (i + 1) → Bool => (g • List.ofFn f).getD i false) ∘
          (fun x : Ray => fun j : Fin (i + 1) => x j) := rfl
    rw [this]
    exact continuous_of_discreteTopology.comp (continuous_pi fun j => continuous_apply _)

/-- pp. 18, 34: the ray `o = 1^∞`. -/
def oneRay : Ray := fun _ => true

/-- p. 18: `x` is cofinal with `1^∞`: all but finitely many digits of `x` are `1`. -/
def IsCofinal (x : Ray) : Prop := ∀ᶠ n in Filter.atTop, x n = true

/-- p. 9: the ray `ux`, the vertex `u` followed by the ray `x`. -/
def prepend (u : List Bool) (x : Ray) : Ray :=
  fun i => if h : i < u.length then u[i] else x (i - u.length)

/-- p. 35: `𝔰ⁿx = x_{n+1}x_{n+2}…`, the ray with its first `n` digits deleted. -/
def shiftRay (x : Ray) (n : ℕ) : Ray := fun i => x (i + n)

/-- p. 9: `|u ∧ x|`, the length of the longest common prefix of a vertex `u` and a ray `x`. -/
def commonPrefixLength (u : List Bool) (x : Ray) : ℕ :=
  ((u.zip (rayPrefix x u.length)).takeWhile fun p => p.1 = p.2).length

/-! ### Sections, stabilizers, rigid stabilizers, `ι`, finitary automorphisms -/

/-- p. 13: the section `g_v` of `g` at the vertex `v` for the right action, defined by
`(v y)·g = (v·g)(y·g_v)`. -/
def sec (g : BinaryTreeAut) (v : List Bool) : BinaryTreeAut := (treeSection g⁻¹ v)⁻¹

theorem append_vertex_smul (g : BinaryTreeAut) (v w : List Bool) :
    (v ++ w) <• g = (v <• g) ++ (w <• sec g v) := by
  rw [vertex_smul_def, vertex_smul_def, vertex_smul_def, sec, inv_inv]
  exact (BinaryTreeAut.append_drop g⁻¹ v w).symm

theorem sec_eq_one_iff (g : BinaryTreeAut) (v : List Bool) :
    sec g v = 1 ↔ ∀ w : List Bool, (v ++ w) <• g = (v <• g) ++ w := by
  constructor
  · intro h w
    rw [append_vertex_smul, h]
    rfl
  · intro h
    have key : ∀ w : List Bool, w <• sec g v = w := by
      intro w
      have := h w
      rw [append_vertex_smul] at this
      exact List.append_cancel_left this
    apply Subtype.ext
    apply Equiv.ext
    intro w
    have := key ((sec g v : Equiv.Perm (List Bool)) w)
    rw [vertex_smul_def] at this
    simpa using this.symm

/-- p. 13: `St_K(L_n)`, the elements of `K` fixing every vertex of level `n`. -/
def levelStab (K : Subgroup BinaryTreeAut) (n : ℕ) : Subgroup BinaryTreeAut :=
  K ⊓ { carrier := {g | ∀ v : List Bool, v.length = n → v <• g = v}
        mul_mem' := fun {a b} ha hb v hv => by
          simp only [Set.mem_ofPred_eq] at ha hb
          rw [vertex_smul_mul, ha v hv, hb v hv]
        one_mem' := fun v _ => one_smul _ v
        inv_mem' := fun {a} ha v hv => by
          simp only [Set.mem_ofPred_eq] at ha
          conv_lhs => rw [← ha v hv]
          rw [← vertex_smul_mul, mul_inv_cancel]
          exact one_smul _ v }

/-- p. 13: `Rist_K(u)`, the elements of `K` fixing every vertex that does not have `u` as a
prefix. -/
def rist (K : Subgroup BinaryTreeAut) (u : List Bool) : Subgroup BinaryTreeAut :=
  K ⊓ { carrier := {g | ∀ v : List Bool, ¬ u <+: v → v <• g = v}
        mul_mem' := fun {a b} ha hb v hv => by
          simp only [Set.mem_ofPred_eq] at ha hb
          rw [vertex_smul_mul, ha v hv, hb v hv]
        one_mem' := fun v _ => one_smul _ v
        inv_mem' := fun {a} ha v hv => by
          simp only [Set.mem_ofPred_eq] at ha
          conv_lhs => rw [← ha v hv]
          rw [← vertex_smul_mul, mul_inv_cancel]
          exact one_smul _ v }

/-- The underlying map of `ι(h, u)` on vertices: `u w ↦ u h(w)`, and the identity on vertices
without the prefix `u`. -/
def iotaFun (h : BinaryTreeAut) (u w : List Bool) : List Bool :=
  if u <+: w then u ++ (h : Equiv.Perm (List Bool)) (w.drop u.length) else w

theorem iotaFun_inv (h : BinaryTreeAut) (u w : List Bool) :
    iotaFun h⁻¹ u (iotaFun h u w) = w := by
  unfold iotaFun
  by_cases hw : u <+: w
  · obtain ⟨t, rfl⟩ := hw
    simp
  · simp [hw]

theorem length_iotaFun (h : BinaryTreeAut) (u w : List Bool) :
    (iotaFun h u w).length = w.length := by
  unfold iotaFun
  split_ifs with hw
  · obtain ⟨t, rfl⟩ := hw
    simp [h.2.1]
  · rfl

theorem iotaFun_prefix_iff (h : BinaryTreeAut) (u v w : List Bool) :
    v <+: w ↔ iotaFun h u v <+: iotaFun h u w := by
  unfold iotaFun
  by_cases hv : u <+: v <;> by_cases hw : u <+: w
  · obtain ⟨s, rfl⟩ := hv
    obtain ⟨t, rfl⟩ := hw
    simp only [List.prefix_append, if_true, List.drop_left', List.prefix_append_right_inj]
    simpa using h.2.2 s t
  · simp only [hv, hw, if_true, if_false]
    constructor
    · intro hvw; exact absurd (hv.trans hvw) hw
    · intro hvw; exact absurd ((List.prefix_append _ _).trans hvw) hw
  · obtain ⟨t, rfl⟩ := hw
    simp only [hv, List.prefix_append, if_true, if_false]
    have key : ∀ z : List Bool, v <+: u ++ z ↔ v <+: u := by
      intro z
      constructor
      · intro hz
        rcases List.prefix_or_prefix_of_prefix hz (List.prefix_append u z) with h1 | h1
        · exact h1
        · exact absurd h1 hv
      · intro hz; exact hz.trans (List.prefix_append u z)
    rw [key, key]
  · simp [hv, hw]

/-- (2.1), p. 14: `ι(h, u)`, the automorphism acting as `h` on the subtree below `u` and
trivially elsewhere: `(u y)·ι(h, u) = u (y·h)`. -/
def iota (h : BinaryTreeAut) (u : List Bool) : BinaryTreeAut :=
  ⟨{ toFun := iotaFun h u
     invFun := iotaFun h⁻¹ u
     left_inv := iotaFun_inv h u
     right_inv := fun w => by simpa using iotaFun_inv h⁻¹ u w },
   fun w => length_iotaFun h u w, fun v w => iotaFun_prefix_iff h u v w⟩

theorem sec_eq_one_of_le (g : BinaryTreeAut) {n m : ℕ} (hnm : n ≤ m)
    (hg : ∀ v : List Bool, v.length = n → sec g v = 1) :
    ∀ v : List Bool, v.length = m → sec g v = 1 := by
  intro v hv
  rw [sec_eq_one_iff]
  intro w
  have hsplit : v = v.take n ++ v.drop n := (List.take_append_drop n v).symm
  have h1 := (sec_eq_one_iff g (v.take n)).1 (hg _ (by simp [hv, hnm]))
  rw [hsplit, List.append_assoc, h1, h1]
  simp

/-- p. 18: the group `L` of finitary automorphisms: those `g` for which there is a level `n` such
that the section `g_v` is trivial for every vertex `v` of level `n`. -/
def finitary : Subgroup BinaryTreeAut where
  carrier := {g | ∃ n, ∀ v : List Bool, v.length = n → sec g v = 1}
  mul_mem' := by
    rintro g h ⟨n, hn⟩ ⟨m, hm⟩
    refine ⟨max n m, fun v hv => ?_⟩
    have hg := sec_eq_one_of_le g (le_max_left n m) hn
    have hh := sec_eq_one_of_le h (le_max_right n m) hm
    rw [sec_eq_one_iff]
    intro w
    rw [vertex_smul_mul, vertex_smul_mul, (sec_eq_one_iff g v).1 (hg v hv),
      (sec_eq_one_iff h _).1 (hh _ (by rw [length_vertex_smul, hv]))]
  one_mem' := ⟨0, fun v _ => by
    rw [sec_eq_one_iff]; intro w; rfl⟩
  inv_mem' := by
    rintro g ⟨n, hn⟩
    refine ⟨n, fun v hv => ?_⟩
    rw [sec_eq_one_iff]
    intro w
    have hu : (v <• g⁻¹).length = n := by rw [length_vertex_smul, hv]
    have h1 := (sec_eq_one_iff g _).1 (hn _ hu) w
    rw [vertex_smul_inv_smul] at h1
    rw [← h1, vertex_smul_smul_inv]

/-! ### The groups `G_ω` -/

/-- p. 14: the non-identity elements `b, c, d` of the four-group `{id, b, c, d}`. -/
inductive BCD
  | b
  | c
  | d
  deriving DecidableEq

/-- p. 14: the letters `0, 1, 2` "vanish on `d, c, b` respectively": `killedBy i` is the
element of `{b, c, d}` on which the letter `i` vanishes. -/
def BCD.killedBy : Fin 3 → BCD
  | 0 => .d
  | 1 => .c
  | 2 => .b

/-- p. 14: the value `ω_n(γ)` of the letter `i` at `γ ∈ {b, c, d}`: `true` for `a`, `false` for
`id`. -/
def letterValue (i : Fin 3) (γ : BCD) : Bool := γ ≠ BCD.killedBy i

/-- p. 14: the shifted string `𝔰^k ω = ω_k ω_{k+1} …`. -/
def shiftSeq (ω : ℕ → Fin 3) (k : ℕ) : ℕ → Fin 3 := fun n => ω (n + k)

/-- p. 14: the action of `γ_ω` (`γ ∈ {b, c, d}`) on vertices, by the wreath recursion
`ψ(γ_ω) = (ω_0(γ), γ_{𝔰ω})`: on the subtree of `0` it acts as `a` or `id` according to
`ω_0(γ)`, and on the subtree of `1` as `γ_{𝔰ω}`. -/
def genFun (ω : ℕ → Fin 3) (γ : BCD) : List Bool → List Bool
  | [] => []
  | false :: w => false :: (if letterValue (ω 0) γ then grigAFun w else w)
  | true :: w => true :: genFun (shiftSeq ω 1) γ w

theorem genFun_involutive (ω : ℕ → Fin 3) (γ : BCD) : Function.Involutive (genFun ω γ) := by
  intro w
  induction w generalizing ω with
  | nil => rfl
  | cons x w ih =>
    cases x
    · by_cases h : letterValue (ω 0) γ <;> simp [genFun, h, grigAFun_involutive w]
    · simp [genFun, ih]

theorem length_genFun (ω : ℕ → Fin 3) (γ : BCD) (w : List Bool) :
    (genFun ω γ w).length = w.length := by
  induction w generalizing ω with
  | nil => rfl
  | cons x w ih =>
    cases x
    · by_cases h : letterValue (ω 0) γ <;> simp [genFun, h, grigAFun_length]
    · simp [genFun, ih]

theorem genFun_prefix (ω : ℕ → Fin 3) (γ : BCD) (v : List Bool) :
    ∀ w, v <+: w → genFun ω γ v <+: genFun ω γ w := by
  induction v generalizing ω with
  | nil => intro w _; simp [genFun]
  | cons x v ih =>
    intro w h
    obtain ⟨t, rfl⟩ := h
    cases x
    · by_cases hl : letterValue (ω 0) γ
      · simp only [List.cons_append, genFun, hl, if_true, List.cons_prefix_cons, true_and]
        exact grigAFun_prefix ⟨t, rfl⟩
      · simp only [List.cons_append, genFun, hl, Bool.false_eq_true, if_false,
          List.cons_prefix_cons, true_and]
        exact ⟨t, rfl⟩
    · simp only [List.cons_append, genFun, List.cons_prefix_cons, true_and]
      exact ih (shiftSeq ω 1) (v ++ t) ⟨t, rfl⟩

theorem genFun_prefix_iff (ω : ℕ → Fin 3) (γ : BCD) (v w : List Bool) :
    v <+: w ↔ genFun ω γ v <+: genFun ω γ w :=
  ⟨genFun_prefix ω γ v w, fun h => by
    simpa [genFun_involutive ω γ v, genFun_involutive ω γ w] using genFun_prefix ω γ _ _ h⟩

/-- p. 14: the generators `b_ω, c_ω, d_ω` of `G_ω`, as (involutive) automorphisms of the binary
tree. -/
def gen (ω : ℕ → Fin 3) (γ : BCD) : BinaryTreeAut :=
  ⟨(genFun_involutive ω γ).toPerm _, length_genFun ω γ, genFun_prefix_iff ω γ⟩

/-- p. 14: the generating set `S = {a, b_ω, c_ω, d_ω}`. -/
def gens (ω : ℕ → Fin 3) : Set BinaryTreeAut := {grigA, gen ω .b, gen ω .c, gen ω .d}

/-- p. 14: the Grigorchuk group `G_ω`, the subgroup of `Aut(T)` generated by `a, b_ω, c_ω, d_ω`. -/
def grigorchuk (ω : ℕ → Fin 3) : Subgroup BinaryTreeAut := Subgroup.closure (gens ω)

/-- p. 14: `S` as a subset of `G_ω`. -/
def genSet (ω : ℕ → Fin 3) : Set (grigorchuk ω) := Subtype.val ⁻¹' gens ω

/-- p. 14: the string `(012)^∞` of the first Grigorchuk group `G_012`. -/
def firstString : ℕ → Fin 3 := fun n => ⟨n % 3, Nat.mod_lt _ (by norm_num)⟩

/-! ### Words and the substitutions `ζ_i` -/

/-- The letters `a, b, c, d` of words. -/
inductive Gen4
  | a
  | b
  | c
  | d
  deriving DecidableEq

/-- A word over `{a, b, c, d}` read in `G_{𝔰^k ω}`: the product of `a, b_{𝔰^k ω}, c_{𝔰^k ω},
d_{𝔰^k ω}` in the order written, which acts on the right letter by letter. -/
def evalWord (ω : ℕ → Fin 3) (k : ℕ) (w : List Gen4) : BinaryTreeAut :=
  (w.map fun
    | .a => grigA
    | .b => gen (shiftSeq ω k) .b
    | .c => gen (shiftSeq ω k) .c
    | .d => gen (shiftSeq ω k) .d).prod

/-- p. 15: the alphabet `{ab, ac, ad}`. -/
inductive APair
  | ab
  | ac
  | ad
  deriving DecidableEq

/-- The word over `{a, b, c, d}` spelled by a letter of `{ab, ac, ad}`. -/
def APair.toWord : APair → List Gen4
  | .ab => [.a, .b]
  | .ac => [.a, .c]
  | .ad => [.a, .d]

/-- (2.2), p. 15: the substitutions `ζ_0, ζ_1, ζ_2` on the letters `ab, ac, ad`. -/
def zetaPair : Fin 3 → APair → List APair
  | 0, .ab => [.ab, .ab]
  | 0, .ac => [.ac, .ac]
  | 0, .ad => [.ab, .ad, .ac]
  | 1, .ab => [.ab, .ab]
  | 1, .ac => [.ad, .ac, .ab]
  | 1, .ad => [.ad, .ad]
  | 2, .ab => [.ac, .ab, .ad]
  | 2, .ac => [.ac, .ac]
  | 2, .ad => [.ad, .ad]

/-- (2.2), p. 15: `ζ_i` on words over `{ab, ac, ad}`. -/
def zetaWord (i : Fin 3) (w : List APair) : List APair := w.flatMap (zetaPair i)

/-- A word over `{ab, ac, ad}` and their inverses (an element of the free group on `APair`), read
in `G_{𝔰^k ω}`. -/
def evalFree (ω : ℕ → Fin 3) (k : ℕ) : FreeGroup APair →* BinaryTreeAut :=
  FreeGroup.lift fun p => evalWord ω k p.toWord

/-- `ζ_i` on the free group on `{ab, ac, ad}`. -/
def zetaFree (i : Fin 3) : FreeGroup APair →* FreeGroup APair :=
  FreeGroup.lift fun p => ((zetaPair i p).map FreeGroup.of).prod

open Classical in
/-- p. 15: `ζ̂_{ω_n}` on group elements: an element `g` of `G_{𝔰^{n+1} ω}` that is the value of a
word over `{ab, ac, ad}` and their inverses is sent to the value in `G_{𝔰^n ω}` of `ζ_{ω_n}` of a
chosen such word; any other `g` is sent to `1`. -/
noncomputable def zetaHat (ω : ℕ → Fin 3) (n : ℕ) (g : BinaryTreeAut) : BinaryTreeAut :=
  if h : ∃ w : FreeGroup APair, evalFree ω (n + 1) w = g then
    evalFree ω n (zetaFree (ω n) h.choose)
  else 1

/-! ### The matrices `M_i`, `L^ω_n`, and the constants `λ_0`, `α_0` -/

/-- p. 56: the matrices `M_0, M_1, M_2` of the substitutions `ζ_0, ζ_1, ζ_2`, in the coordinates
`(ab, ac, ad)`. -/
def substMatrix : Fin 3 → Matrix (Fin 3) (Fin 3) ℕ
  | 0 => !![2, 0, 1; 0, 2, 1; 0, 0, 1]
  | 1 => !![2, 1, 0; 0, 1, 0; 0, 1, 2]
  | 2 => !![1, 0, 0; 1, 2, 0; 1, 0, 2]

/-- (8.1), p. 57: `L^ω_n = (1 1 1) M_{ω_0} ⋯ M_{ω_{n-1}} (1 1 1)^T`. -/
def lengthL (ω : ℕ → Fin 3) (n : ℕ) : ℕ :=
  Matrix.vecMul (fun _ => 1) (List.ofFn fun i : Fin n => substMatrix (ω i)).prod ⬝ᵥ fun _ => 1

/-- p. 28: the matrix `M` of the substitution `ζ` of `G_012`. -/
def matrixM : Matrix (Fin 3) (Fin 3) ℕ := !![1, 2, 0; 1, 0, 2; 1, 0, 0]

/-- p. 2: `λ_0`, the supremum of the positive real roots of `X³ - X² - 2X - 4`. -/
noncomputable def lambda0 : ℝ := sSup {x : ℝ | 0 < x ∧ x ^ 3 - x ^ 2 - 2 * x - 4 = 0}

/-- p. 2: `α_0 = log 2 / log λ_0`. -/
noncomputable def alpha0 : ℝ := Real.log 2 / Real.log lambda0

/-! ### Assumption `Fr(D)` -/

/-- Notation 7.1, p. 34: Assumption `Fr(D)`: for every `k ⩾ 0`, the block `ω_{kD} … ω_{kD+D-1}`
contains `201` or `211`. -/
def SatisfiesFr (D : ℕ) (ω : ℕ → Fin 3) : Prop :=
  ∀ k, ∃ m, m + 3 ≤ D ∧ ω (k * D + m) = 2 ∧ ω (k * D + m + 2) = 1 ∧
    (ω (k * D + m + 1) = 0 ∨ ω (k * D + m + 1) = 1)

/-- Notation 7.1, p. 34: `m_k`, the smallest `m ∈ {0, …, D - 3}` with
`ω_{kD+m} ω_{kD+m+1} ω_{kD+m+2} ∈ {201, 211}` (`0` if there is none). -/
noncomputable def frM (D : ℕ) (ω : ℕ → Fin 3) (k : ℕ) : ℕ :=
  sInf {m | m + 3 ≤ D ∧ ω (k * D + m) = 2 ∧ ω (k * D + m + 2) = 1 ∧
    (ω (k * D + m + 1) = 0 ∨ ω (k * D + m + 1) = 1)}

/-- Notation 7.1, p. 34: `I_ω = {kD + m_k + 3 : k ⩾ 0}`. -/
def frI (D : ℕ) (ω : ℕ → Fin 3) : Set ℕ := {i | ∃ k, i = k * D + frM D ω k + 3}

/-! ### The Schreier graph of `1^∞` and the Gray code -/

/-- p. 34: `d_{𝒮_ω}(x, y)`, the distance in the Schreier graph of `G_ω` (edges `x — x·s`,
`s ∈ S`): the least `n` such that `y = x·g` for a product `g` of at most `n` factors, each in `S`
or with its inverse in `S` (`0` if there is none). -/
noncomputable def schreierDist (ω : ℕ → Fin 3) (x y : Ray) : ℕ :=
  sInf {n | ∃ g ∈ Chou.wordBall (gens ω) n, y = x <• g}

/-- Fact 7.3, p. 35: `n(x) = max{k : x_k = 0}`, with the paper's 1-based index `k` (Lean's digit
`x (k - 1)`); `0` when the set is empty or unbounded. -/
noncomputable def maxZeroIndex (x : Ray) : ℕ := sSup {k | 1 ≤ k ∧ x (k - 1) = false}

/-- p. 34, with suffix sums: the Gray code of a finite word `x_1 … x_m` (followed by `1^∞`), the
number with binary digits `x̄_i = x̌_i + x̌_{i+1} + ⋯ + x̌_m mod 2`, `x̌_k = 1 - x_k`, where `x̄_1`
is the least significant digit. -/
def grayList : List Bool → ℕ
  | [] => 0
  | b :: v => (b :: v).count false % 2 + 2 * grayList v

/-- p. 34, with suffix sums: the Gray code `x̄` of a ray `x`, as a number: `grayList` of the prefix
`x_1 … x_{n(x)}` of `x` up to its last `0` (so `0` for `x = 1^∞`, and for `x` not cofinal with
`1^∞`). -/
noncomputable def grayCode (x : Ray) : ℕ := grayList (rayPrefix x (maxZeroIndex x))

/-! ### Germs -/

/-- Example 3.2, p. 18: `g` has `γ`-germ at `x`: there is a level `n` such that
`x = x_1 … x_n 1^∞` and the section of `g` at `x_1 … x_n` is `γ_{𝔰^n ω}`. -/
def HasGermAt (ω : ℕ → Fin 3) (γ : BCD) (g : BinaryTreeAut) (x : Ray) : Prop :=
  ∃ n, shiftRay x n = oneRay ∧ sec g (rayPrefix x n) = gen (shiftSeq ω n) γ

/-- Example 3.2, p. 18: `⟨γ⟩`, the subgroup of the group of germs at `o = 1^∞` generated by the
germ of `γ_ω`. -/
noncomputable def germLetterSubgroup (ω : ℕ → Fin 3) (γ : BCD) :
    Subgroup (GermGroup (H := BinaryTreeAut) oneRay) :=
  Subgroup.zpowers (germ oneRay (gen ω γ))

/-- Example 3.2, p. 18: the groupoid `ℋ(⟨γ⟩)` of `⟨γ⟩`-germs of `G_ω` (`ℋ^b` for `γ = b`), with
the finitary automorphisms as the auxiliary group and `o = 1^∞`. -/
noncomputable def letterGerms (ω : ℕ → Fin 3) (γ : BCD) : Set (BinaryTreeAut × Ray) :=
  germSubgroupoid (grigorchuk ω) finitary oneRay (germLetterSubgroup ω γ)

/-- p. 34: the orbit `1^∞·G_ω`, the vertex set of the Schreier graph `𝒮_ω`. -/
abbrev orbitOne (ω : ℕ → Fin 3) : Set Ray := rightOrbit (grigorchuk ω) oneRay

/-- p. 34: `d_𝒮` as a real-valued function on the orbit `1^∞·G_ω`. -/
noncomputable def orbitDist (ω : ℕ → Fin 3) (x y : orbitOne ω) : ℝ := schreierDist ω x y

/-! ### Spherically symmetric rooted trees `T_d` (p. 13) -/

/-- p. 13: the vertices `v = v_1 … v_n` of the spherically symmetric rooted tree `T_d`, as lists
with `v_j ∈ {0, …, d_j - 1}` (Lean's `v[i]` and `d i` are the paper's `v_{i+1}` and `d_{i+1}`). -/
abbrev SphericalVertex (d : ℕ → ℕ) : Type := {v : List ℕ // ∀ i (h : i < v.length), v[i] < d i}

/-- p. 13: `Aut(T_d)`, the automorphisms of `T_d` fixing the root: permutations of the vertices
that preserve length and the prefix order in both directions. -/
def SphericalTreeAut (d : ℕ → ℕ) : Subgroup (Equiv.Perm (SphericalVertex d)) where
  carrier := {σ | (∀ v, (σ v).1.length = v.1.length) ∧ ∀ v w, v.1 <+: w.1 ↔ (σ v).1 <+: (σ w).1}
  mul_mem' := by
    rintro σ τ ⟨hσl, hσ⟩ ⟨hτl, hτ⟩
    refine ⟨fun v => ?_, fun v w => ?_⟩
    · simp [hσl, hτl]
    · simp only [Equiv.Perm.coe_mul, Function.comp_apply]
      rw [hτ v w, hσ]
  one_mem' := ⟨fun v => rfl, fun v w => Iff.rfl⟩
  inv_mem' := by
    rintro σ ⟨hσl, hσ⟩
    refine ⟨fun v => ?_, fun v w => ?_⟩
    · have := hσl (σ⁻¹ v); simp at this; exact this.symm
    · rw [hσ (σ⁻¹ v) (σ⁻¹ w)]; simp

section Spherical

variable {d : ℕ → ℕ}

/-- p. 9, p. 13: the right action `v·g` of `g ∈ Aut(T_d)` on vertices, `op g • v := g⁻¹ v`. -/
instance sphericalVertexRightAction : MulAction (SphericalTreeAut d)ᵐᵒᵖ (SphericalVertex d) where
  smul g v := ((g.unop⁻¹ : SphericalTreeAut d) : Equiv.Perm (SphericalVertex d)) v
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

theorem length_sphericalVertex_smul (g : SphericalTreeAut d) (v : SphericalVertex d) :
    (v <• g).1.length = v.1.length :=
  (g⁻¹).2.1 v

theorem sphericalVertex_smul_prefix_iff (g : SphericalTreeAut d) (v w : SphericalVertex d) :
    (v <• g).1 <+: (w <• g).1 ↔ v.1 <+: w.1 :=
  ((g⁻¹).2.2 v w).symm

theorem sphericalVertex_smul_smul_inv (g : SphericalTreeAut d) (v : SphericalVertex d) :
    v <• g <• g⁻¹ = v := by
  rw [← mul_smul, ← MulOpposite.op_mul, mul_inv_cancel]; exact one_smul _ v

/-- The vertex `v y` of `T_d`, for a vertex `v` of level `n` and a vertex `y` of `T_{𝔰ⁿ d}`. -/
def sphericalAppend (v : SphericalVertex d) {n : ℕ} (hv : v.1.length = n)
    (y : SphericalVertex (fun i => d (i + n))) : SphericalVertex d :=
  ⟨v.1 ++ y.1, fun i hi => by
    subst hv
    by_cases h : i < v.1.length
    · rw [List.getElem_append_left h]; exact v.2 i h
    · rw [List.getElem_append_right (by omega)]
      have := y.2 (i - v.1.length) (by simp at hi; omega)
      simpa [show i - v.1.length + v.1.length = i by omega] using this⟩

/-- The vertex `w_{n+1} w_{n+2} …` of `T_{𝔰ⁿ d}` obtained by deleting the first `n` digits of a
vertex `w` of `T_d`. -/
def sphericalDrop (w : SphericalVertex d) (n : ℕ) : SphericalVertex (fun i => d (i + n)) :=
  ⟨w.1.drop n, fun i hi => by
    rw [List.getElem_drop]
    have := w.2 (n + i) (by simp at hi; omega)
    simpa [Nat.add_comm] using this⟩

theorem sphericalDrop_append (v : SphericalVertex d) {n : ℕ} (hv : v.1.length = n)
    (y : SphericalVertex (fun i => d (i + n))) : sphericalDrop (sphericalAppend v hv y) n = y := by
  apply Subtype.ext
  simp [sphericalDrop, sphericalAppend, ← hv]

theorem sphericalAppend_drop (v w : SphericalVertex d) {n : ℕ} (hv : v.1.length = n)
    (hvw : v.1 <+: w.1) : sphericalAppend v hv (sphericalDrop w n) = w := by
  apply Subtype.ext
  obtain ⟨t, ht⟩ := hvw
  simp only [sphericalAppend, sphericalDrop, ← ht, ← hv, List.drop_left']

theorem prefix_iff_drop_prefix {v z z' : List ℕ} (hz : v <+: z) (hz' : v <+: z') :
    z <+: z' ↔ z.drop v.length <+: z'.drop v.length := by
  obtain ⟨s, rfl⟩ := hz
  obtain ⟨s', rfl⟩ := hz'
  simp

theorem sphericalVertex_inv_smul_smul (g : SphericalTreeAut d) (v : SphericalVertex d) :
    v <• g⁻¹ <• g = v := by
  rw [← mul_smul, ← MulOpposite.op_mul, inv_mul_cancel]; exact one_smul _ v

/-- The action of the section `g_v` on vertices `y` of `T_{𝔰^{|v|} d}`:
`y·g_v` is `(v y)·g` with the prefix `v·g` deleted. -/
def sphericalSecSmul (g : SphericalTreeAut d) (v : SphericalVertex d)
    (y : SphericalVertex (fun i => d (i + v.1.length))) :
    SphericalVertex (fun i => d (i + v.1.length)) :=
  sphericalDrop (sphericalAppend v rfl y <• g) v.1.length

/-- The inverse of `sphericalSecSmul g v`: `y ↦ ((v·g) y)·g⁻¹` with the prefix `v` deleted. -/
def sphericalSecInvSmul (g : SphericalTreeAut d) (v : SphericalVertex d)
    (y : SphericalVertex (fun i => d (i + v.1.length))) :
    SphericalVertex (fun i => d (i + v.1.length)) :=
  sphericalDrop (sphericalAppend (v <• g) (length_sphericalVertex_smul g v) y <• g⁻¹) v.1.length

theorem prefix_sphericalSecInvSmul_aux (g : SphericalTreeAut d) (v : SphericalVertex d)
    (y : SphericalVertex (fun i => d (i + v.1.length))) :
    v.1 <+: (sphericalAppend (v <• g) (length_sphericalVertex_smul g v) y <• g⁻¹).1 := by
  have h1 : (v <• g).1 <+: (sphericalAppend (v <• g) (length_sphericalVertex_smul g v) y).1 :=
    List.prefix_append _ _
  have h2 := (sphericalVertex_smul_prefix_iff g⁻¹ _ _).2 h1
  rwa [sphericalVertex_smul_smul_inv] at h2

theorem prefix_sphericalSecSmul_aux (g : SphericalTreeAut d) (v : SphericalVertex d)
    (y : SphericalVertex (fun i => d (i + v.1.length))) :
    (v <• g).1 <+: (sphericalAppend v rfl y <• g).1 :=
  (sphericalVertex_smul_prefix_iff g _ _).2 (List.prefix_append _ _)

theorem sphericalSecSmul_inv (g : SphericalTreeAut d) (v : SphericalVertex d)
    (y : SphericalVertex (fun i => d (i + v.1.length))) :
    sphericalSecSmul g v (sphericalSecInvSmul g v y) = y := by
  unfold sphericalSecSmul sphericalSecInvSmul
  rw [sphericalAppend_drop v _ rfl (prefix_sphericalSecInvSmul_aux g v y),
    sphericalVertex_inv_smul_smul]
  exact sphericalDrop_append _ _ y

theorem sphericalSecInvSmul_smul (g : SphericalTreeAut d) (v : SphericalVertex d)
    (y : SphericalVertex (fun i => d (i + v.1.length))) :
    sphericalSecInvSmul g v (sphericalSecSmul g v y) = y := by
  unfold sphericalSecSmul sphericalSecInvSmul
  rw [sphericalAppend_drop (v <• g) _ (length_sphericalVertex_smul g v)
    (prefix_sphericalSecSmul_aux g v y), sphericalVertex_smul_smul_inv]
  exact sphericalDrop_append _ _ y

/-- p. 13: the section `g_v ∈ Aut(T_{𝔰^{|v|} d})` of `g ∈ Aut(T_d)` at the vertex `v`, for the
right action: `(v y)·g = (v·g)(y·g_v)`. -/
def sphericalSec (g : SphericalTreeAut d) (v : SphericalVertex d) :
    SphericalTreeAut (fun i => d (i + v.1.length)) :=
  ⟨{ toFun := sphericalSecInvSmul g v
     invFun := sphericalSecSmul g v
     left_inv := sphericalSecSmul_inv g v
     right_inv := sphericalSecInvSmul_smul g v },
   fun y => by
     show (sphericalSecInvSmul g v y).1.length = y.1.length
     unfold sphericalSecInvSmul sphericalDrop
     rw [List.length_drop, length_sphericalVertex_smul]
     simp [sphericalAppend, length_sphericalVertex_smul],
   fun y y' => by
     show y.1 <+: y'.1 ↔ (sphericalSecInvSmul g v y).1 <+: (sphericalSecInvSmul g v y').1
     unfold sphericalSecInvSmul sphericalDrop
     simp only
     rw [← prefix_iff_drop_prefix (prefix_sphericalSecInvSmul_aux g v y)
       (prefix_sphericalSecInvSmul_aux g v y'), sphericalVertex_smul_prefix_iff]
     simp [sphericalAppend]⟩

/-- The first-level vertex `j` of `T_d`. -/
def sphericalLetter (j : Fin (d 0)) : SphericalVertex d :=
  ⟨[j.1], fun i hi => by simp at hi; subst hi; simp⟩

/-- p. 13: the root permutation `τ_1(g)` of `g ∈ Aut(T_d)`, as a map on `{0, …, d_1 - 1}` (Lean's
`Fin (d 0)`): `j ↦` the digit of the first-level vertex `j·g`. -/
def rootPerm (g : SphericalTreeAut d) (j : Fin (d 0)) : Fin (d 0) :=
  ⟨(sphericalLetter j <• g).1.headD 0, by
    have hl : (sphericalLetter j <• g).1.length = 1 := length_sphericalVertex_smul g _
    obtain ⟨k, hk⟩ : ∃ k, (sphericalLetter j <• g).1 = [k] := List.length_eq_one_iff.mp hl
    have := (sphericalLetter j <• g).2 0 (by rw [hl]; norm_num)
    simp only [hk, List.headD_cons]
    simpa [hk] using this⟩

/-- p. 13: the boundary `∂T_d`, the rays `x = x_1 x_2 …` with `x_j ∈ {0, …, d_j - 1}` (Lean's
`x i` is the paper's `x_{i+1}`). -/
abbrev SphericalRay (d : ℕ → ℕ) : Type := {x : ℕ → ℕ // ∀ i, x i < d i}

/-- `x_1 … x_n`, the prefix of length `n` of a ray of `T_d`. -/
def sphericalRayPrefix (x : SphericalRay d) (n : ℕ) : SphericalVertex d :=
  ⟨List.ofFn fun i : Fin n => x.1 i, fun i hi => by simpa using x.2 i⟩

theorem getElem_sphericalRayPrefix (x : SphericalRay d) (n i : ℕ)
    (h : i < (sphericalRayPrefix x n).1.length) : (sphericalRayPrefix x n).1[i] = x.1 i := by
  simp [sphericalRayPrefix]

theorem sphericalRayPrefix_prefix (x : SphericalRay d) {m n : ℕ} (h : m ≤ n) :
    (sphericalRayPrefix x m).1 <+: (sphericalRayPrefix x n).1 := by
  rw [List.prefix_iff_eq_take]
  apply List.ext_getElem
  · simp [sphericalRayPrefix, h]
  · intro i h1 h2
    simp [sphericalRayPrefix]

theorem getD_sphericalVertex_smul_lt (g : (SphericalTreeAut d)ᵐᵒᵖ) (x : SphericalRay d) (i : ℕ) :
    (g • sphericalRayPrefix x (i + 1)).1.getD i 0 < d i := by
  have hl : (g • sphericalRayPrefix x (i + 1)).1.length = i + 1 := by
    rw [show g = MulOpposite.op g.unop from rfl, length_sphericalVertex_smul]
    simp [sphericalRayPrefix]
  rw [List.getD_eq_getElem _ _ (by omega)]
  exact (g • sphericalRayPrefix x (i + 1)).2 i (by omega)

instance sphericalRaySMul : SMul (SphericalTreeAut d)ᵐᵒᵖ (SphericalRay d) :=
  ⟨fun g x => ⟨fun i => (g • sphericalRayPrefix x (i + 1)).1.getD i 0,
    getD_sphericalVertex_smul_lt g x⟩⟩

theorem sphericalRayPrefix_smul_aux (g : (SphericalTreeAut d)ᵐᵒᵖ) (x : SphericalRay d) (n : ℕ) :
    sphericalRayPrefix (g • x) n = g • sphericalRayPrefix x n := by
  have hlen : ∀ v : SphericalVertex d, (g • v).1.length = v.1.length := fun v =>
    length_sphericalVertex_smul g.unop v
  apply Subtype.ext
  apply List.ext_getElem
  · simp [sphericalRayPrefix, hlen]
  · intro i h1 h2
    simp only [sphericalRayPrefix, List.getElem_ofFn]
    show (g • sphericalRayPrefix x (i + 1)).1.getD i 0 = _
    have hi : i < (g • sphericalRayPrefix x (i + 1)).1.length := by
      simp [hlen, sphericalRayPrefix]
    have hp : (g • sphericalRayPrefix x (i + 1)).1 <+: (g • sphericalRayPrefix x n).1 :=
      (sphericalVertex_smul_prefix_iff g.unop _ _).2
        (sphericalRayPrefix_prefix x (by simp [sphericalRayPrefix] at h1; omega))
    rw [List.getD_eq_getElem _ _ hi]
    exact hp.getElem hi

/-- The induced right action of `Aut(T_d)` on rays: digit `i` of `x·g` is digit `i` of
`(x_1 … x_{i+1})·g`. -/
instance sphericalRayRightAction : MulAction (SphericalTreeAut d)ᵐᵒᵖ (SphericalRay d) :=
  { (inferInstance : SMul (SphericalTreeAut d)ᵐᵒᵖ (SphericalRay d)) with
    one_smul := fun x => by
      apply Subtype.ext
      funext i
      show (sphericalRayPrefix x (i + 1)).1.getD i 0 = x.1 i
      rw [List.getD_eq_getElem _ _ (by simp [sphericalRayPrefix]), getElem_sphericalRayPrefix]
    mul_smul := fun g h x => by
      apply Subtype.ext
      funext i
      show ((g * h) • sphericalRayPrefix x (i + 1)).1.getD i 0 =
        (g • sphericalRayPrefix (h • x) (i + 1)).1.getD i 0
      rw [sphericalRayPrefix_smul_aux, mul_smul] }

/-- The ray `1^∞` of `T_d`, when every `d_j ⩾ 2`. -/
def sphericalOneRay (d : ℕ → ℕ) (hd : ∀ j, 2 ≤ d j) : SphericalRay d := ⟨fun _ => 1, hd⟩

/-! ### The binary tree as `T_d` with `d ≡ 2` -/

/-- Binary words as vertices of `T_d` with `d ≡ 2`, by the relabelling `false ↦ 0`, `true ↦ 1`. -/
def binaryVertexEquiv : List Bool ≃ SphericalVertex (fun _ => 2) where
  toFun v := ⟨v.map Bool.toNat, fun i hi => by rw [List.getElem_map]; exact Bool.toNat_lt _⟩
  invFun v := v.1.map fun k => decide (k = 1)
  left_inv v := by
    simp only [List.map_map]
    conv_rhs => rw [← List.map_id v]
    apply List.map_congr_left
    intro b _
    cases b <;> rfl
  right_inv v := by
    apply Subtype.ext
    apply List.ext_getElem
    · simp
    · intro i h1 h2
      have := v.2 i h2
      simp only [List.getElem_map]
      generalize v.1[i] = k at this ⊢
      interval_cases k <;> rfl

/-- Binary rays as rays of `T_d` with `d ≡ 2`, by the relabelling `false ↦ 0`, `true ↦ 1`. -/
def binaryRayEquiv : Ray ≃ SphericalRay (fun _ => 2) where
  toFun x := ⟨fun i => (x i).toNat, fun i => Bool.toNat_lt _⟩
  invFun y := fun i => decide (y.1 i = 1)
  left_inv x := by
    funext i
    show decide ((x i).toNat = 1) = x i
    cases x i <;> rfl
  right_inv y := by
    apply Subtype.ext
    funext i
    have := y.2 i
    show (decide (y.1 i = 1)).toNat = y.1 i
    generalize y.1 i = k at this ⊢
    interval_cases k <;> rfl

theorem binaryVertexEquiv_prefix_iff (v w : List Bool) :
    (binaryVertexEquiv v).1 <+: (binaryVertexEquiv w).1 ↔ v <+: w :=
  List.prefix_map_iff_of_injective (fun a b h => by cases a <;> cases b <;> simp_all)

theorem prefix_iff_binaryVertexEquiv_symm (s t : SphericalVertex (fun _ => 2)) :
    s.1 <+: t.1 ↔ binaryVertexEquiv.symm s <+: binaryVertexEquiv.symm t := by
  conv_lhs => rw [← binaryVertexEquiv.apply_symm_apply s, ← binaryVertexEquiv.apply_symm_apply t]
  exact binaryVertexEquiv_prefix_iff _ _

theorem length_binaryVertexEquiv (v : List Bool) : (binaryVertexEquiv v).1.length = v.length := by
  simp [binaryVertexEquiv]

theorem length_binaryVertexEquiv_symm (s : SphericalVertex (fun _ => 2)) :
    (binaryVertexEquiv.symm s).length = s.1.length := by
  simp [binaryVertexEquiv]

/-- The isomorphism from `Aut(T)` of the binary tree to `Aut(T_d)` with `d ≡ 2` given by
conjugating with the relabelling `false ↦ 0`, `true ↦ 1` of vertices. -/
def binaryToSpherical : BinaryTreeAut ≃* SphericalTreeAut (fun _ => 2) where
  toFun g := ⟨binaryVertexEquiv.permCongr g,
    fun s => by
      simp only [Equiv.permCongr_apply, length_binaryVertexEquiv, g.2.1,
        length_binaryVertexEquiv_symm],
    fun s t => by
      simp only [Equiv.permCongr_apply]
      rw [prefix_iff_binaryVertexEquiv_symm, binaryVertexEquiv_prefix_iff, ← g.2.2]⟩
  invFun h := ⟨binaryVertexEquiv.symm.permCongr h,
    fun v => by
      simp only [Equiv.permCongr_apply, Equiv.symm_symm, length_binaryVertexEquiv_symm, h.2.1,
        length_binaryVertexEquiv],
    fun v w => by
      simp only [Equiv.permCongr_apply, Equiv.symm_symm]
      rw [← prefix_iff_binaryVertexEquiv_symm, ← h.2.2, binaryVertexEquiv_prefix_iff]⟩
  left_inv g := by
    apply Subtype.ext; apply Equiv.ext; intro v; simp
  right_inv h := by
    apply Subtype.ext; apply Equiv.ext; intro s; simp
  map_mul' g h := by
    apply Subtype.ext; apply Equiv.ext; intro s; simp

end Spherical

end ErschlerZheng


