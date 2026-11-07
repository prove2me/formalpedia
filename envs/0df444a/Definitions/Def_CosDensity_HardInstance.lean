-- Prove2me | Definitions.Def_CosDensity_HardInstance
-- name    : CosDensity_HardInstance
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:38:26.707466+00:00
-- url     : https://prove2.me/theorems/fc84d513-e9d6-4357-a13d-cecbe4ad4bac
-- title:
--   The hard input of §8: gadgets $\mathcal G_0,\mathcal G_1$, Bob's suffix and $P(z,q)$
-- statement:
--   Fix an integer $p>2$. The construction lives in $\mathbb R^{4m}$, the orthogonal sum of a **code block** $\mathbb R^m$, an **anchor block** with orthonormal basis $e_1,\dots,e_m$, a **balancing block** with basis $g_1,\dots,g_m$ and a **suffix block** with basis $w_1,\dots,w_m$.
--
--   Constants: $c_j=(-1)^{p-j}\binom pj$ for $0\le j\le p$, $\mathcal J_+=\{j:c_j>0\}$, $\mathcal J_-=\{j:c_j<0\}$; $\lambda=\sqrt{2/3}$, $t_0=1/20$, $h=2/(5p)$, $t_j=t_0+jh$, $\mu_j=\sqrt{1-\lambda^2-t_j^2}$.
--
--   Given codewords $a_1,\dots,a_N\in\mathbb R^m$ and a coloring $\chi:[N]\to[m]$, the level-$j$ vectors are
--
--   $$u_{i,j,\sigma}=t_ja_i+\lambda e_{\chi(i)}+\sigma\mu_jg_{\chi(i)},\qquad \sigma\in\{-1,+1\}.\qquad(26)$$
--
--   The **one-gadget** $\mathcal G_1(a_i)$ contains, for each $j\in\mathcal J_+$, $|c_j|$ copies of $u_{i,j,+}$ and $|c_j|$ copies of $u_{i,j,-}$; the **zero-gadget** $\mathcal G_0(a_i)$ does the same for $j\in\mathcal J_-$ ((27)–(28)). Alice's prefix for $z\in\{0,1\}^N$ is $\biguplus_i\mathcal G_{z_i}(a_i)$. For a query $q$, Bob's vectors are $v_\ell=\frac1{\sqrt m}a_q+\sqrt{1-\frac1m}\,w_\ell$, each repeated $L=\lfloor m^{(p-2)/2}\rfloor$ times, and $Q=L\sqrt m$. The hard stream $P(z,q)$ is Alice's prefix followed by Bob's suffix (34).
--
--   Further quantities: $\kappa_p=2\,p!\,h^p$, $\gamma_p=2\sum_{j\in\mathcal J_+}c_jt_j$, $\beta_p=2\lambda\sum_{j\in\mathcal J_+}c_j$; for a vector $s$, $Z_i=\langle a_i,s\rangle$ and $B_i=\lambda\langle e_{\chi(i)},s\rangle$; $V_0(q)=M_p(P(0,q))$; $R_i=1+\sum_{r\ne i}\langle a_i,a_r\rangle$, $R_{\max}=(N/m)^{(p-1)/(p-2)}$; $N=m\lfloor c_Nm^{\rho_p-1}\rfloor$; a coloring is **balanced** if $|\chi^{-1}(c)|=N/m$ for every $c$; the normalized incidence vector of $S\subseteq[m]$ is $\mathbf 1_S/\sqrt{|S|}$.
--
--   These are the objects of the paper's reduction from $\mathrm{INDEX}_N$ to approximating $M_p$.
--
--   **Formalization Note** The ambient space is $\mathbb R^{\mathrm{Fin}\,4\times\mathrm{Fin}\,m}$ with the standard basis vectors of blocks 1, 2, 3 as $e_c,g_c,w_\ell$; any other choice of orthonormal bases is isometric to it. $c_j>0$ exactly when $p-j$ is even. Gadgets and streams are lists in a fixed order (levels ascending; for each level the $+$ copies before the $-$ copies; Bob's $v_1$ copies first); $M_p$ does not depend on the order. Signs are Booleans (true is $+1$). Indices are $0$-based.
-- source:
--   Q. Zhang, Frequency Moments Beyond Equality: Streaming Cosine Density Moments, arXiv:2609.06925 (held version, sha256 f4d4df22…), §8.1 p.29, §8.3 p.30, (26)–(28) p.31, (29) and Lemma 8.6 p.32, §8.5 pp.32–33 ((34), L and Q), §8.6 p.33 ((35), R_max), V_0(q) p.34

import Mathlib
import Definitions.Def_CosDensity_Stream

open scoped RealInnerProductSpace

namespace CosDensity

/-!
# The hard input of §8: sparse codes, finite-difference gadgets and Bob's suffix

Q. Zhang, *Frequency Moments Beyond Equality: Streaming Cosine Density Moments*, arXiv:2609.06925
(held version, sha256 f4d4df22…), §8.1–8.6, pp.29–34 (pdf_page 30–35): notation (§8.1, p.29),
the finite-difference constants (§8.3, p.30), the vectors (26) and gadgets (27)–(28) (§8.4, p.31),
the constants (29) and Lemma 8.6's `κ_p`, `B_i`, `Z_i` (p.32), Bob's vectors, `L`, `Q` and the
stream (34) (§8.5, pp.32–33), and `R_i`, `R_max`, `V_0(q)` (§8.6, pp.33–34).

**Formalization Note.**
* The ambient space of the construction is `ℝ^{4m}`, written `EuclideanSpace ℝ (Fin 4 × Fin m)`:
  block `0` is the code block (a copy of `ℝ^m`), block `1` the anchor block (`e_c = ` standard
  basis vector `(1, c)`), block `2` the balancing block (`g_c = (2, c)`) and block `3` Bob's suffix
  block (`w_ℓ = (3, ℓ)`). The paper fixes arbitrary orthonormal bases of four mutually orthogonal
  blocks; every such choice is isometric to this one.
* Codewords are `a : Fin N → EuclideanSpace ℝ (Fin m)`, embedded in block `0` by `codeVec`; the
  coloring is `χ : Fin N → Fin m`. Indices `i ∈ [N]`, `c ∈ [m]` are `0`-based.
* `coef p j = (−1)^{p−j} C(p, j)` for `0 ≤ j ≤ p`, so `c_j > 0` exactly when `p − j` is even:
  `J₊ = {j ≤ p : Even (p − j)}`, `J₋ = {j ≤ p : Odd (p − j)}`.
* `λ = √(2/3)` (the paper fixes `λ² = 2/3`; `λ > 0`), `t₀ = 1/20`, `h = 2/(5p)`, `t_j = t₀ + j h`,
  `μ_j = √(1 − λ² − t_j²)`.
* A sign `σ ∈ {−1, +1}` is a `Bool` (`true` = `+1`).
* The gadgets (27)–(28) are multisets; here they are lists in a fixed order: levels `j` ascending,
  for each level `|c_j|` copies of `u_{i,j,+}` followed by `|c_j|` copies of `u_{i,j,−}`. The bit
  `b = true` gives the one-gadget `G₁`, `b = false` the zero-gadget `G₀`. `M_p` does not depend on
  the order of a stream.
* Alice's prefix lists the gadgets `G_{z_i}(a_i)` for `i = 0, …, N − 1`; Bob's suffix lists `L`
  copies of `v_0`, then `L` copies of `v_1`, …, as in (34).
* `L = ⌊m^{(p−2)/2}⌋` (a floor on the rendered page) and `N = m ⌊c_N m^{ρ_p − 1}⌋`.
-/

/-- The ambient space `ℝ^{4m}` of the construction (four blocks of dimension `m`). -/
abbrev Amb (m : ℕ) : Type := EuclideanSpace ℝ (Fin 4 × Fin m)

/-- A vector of `ℝ^m` placed in the code block. -/
noncomputable def codeVec {m : ℕ} (a : EuclideanSpace ℝ (Fin m)) : Amb m :=
  WithLp.toLp 2 (fun x : Fin 4 × Fin m => if x.1 = 0 then a x.2 else 0)

/-- The anchor basis vector `e_c`. -/
noncomputable def anchorVec {m : ℕ} (c : Fin m) : Amb m := EuclideanSpace.single (1, c) 1

/-- The balancing basis vector `g_c`. -/
noncomputable def balVec {m : ℕ} (c : Fin m) : Amb m := EuclideanSpace.single (2, c) 1

/-- The suffix basis vector `w_ℓ`. -/
noncomputable def sufVec {m : ℕ} (ℓ : Fin m) : Amb m := EuclideanSpace.single (3, ℓ) 1

/-- The finite-difference coefficient `c_j = (−1)^{p−j} C(p, j)`. -/
def coef (p j : ℕ) : ℝ := (-1) ^ (p - j) * (p.choose j : ℝ)

/-- The local-anchor coefficient `λ`, with `λ² = 2/3`. -/
noncomputable def lam : ℝ := Real.sqrt (2 / 3)

/-- The smallest level coefficient `t₀ = 1/20`. -/
noncomputable def t0 : ℝ := 1 / 20

/-- The level spacing `h = 2/(5p)`. -/
noncomputable def hstep (p : ℕ) : ℝ := 2 / (5 * (p : ℝ))

/-- The level coefficient `t_j = t₀ + j h`. -/
noncomputable def level (p j : ℕ) : ℝ := t0 + (j : ℝ) * hstep p

/-- The balancing coefficient `μ_j = √(1 − λ² − t_j²)`. -/
noncomputable def balCoef (p j : ℕ) : ℝ := Real.sqrt (1 - lam ^ 2 - level p j ^ 2)

/-- The sign `σ ∈ {−1, +1}` encoded by a Boolean (`true ↦ +1`). -/
def signR (σ : Bool) : ℝ := if σ then 1 else -1

/-- The level-`j` gadget vector (26): `u_{i,j,σ} = t_j a_i + λ e_{χ(i)} + σ μ_j g_{χ(i)}`. -/
noncomputable def gadgetVec {N m : ℕ} (p : ℕ) (a : Fin N → EuclideanSpace ℝ (Fin m))
    (χ : Fin N → Fin m) (i : Fin N) (j : ℕ) (σ : Bool) : Amb m :=
  level p j • codeVec (a i) + lam • anchorVec (χ i) + (signR σ * balCoef p j) • balVec (χ i)

/-- The gadget `G_b(a_i)` of (27)–(28): for every level `j ≤ p` with `c_j > 0` (if `b = true`)
or `c_j < 0` (if `b = false`), `|c_j|` copies of `u_{i,j,+}` and `|c_j|` copies of `u_{i,j,−}`. -/
noncomputable def gadget {N m : ℕ} (p : ℕ) (a : Fin N → EuclideanSpace ℝ (Fin m))
    (χ : Fin N → Fin m) (b : Bool) (i : Fin N) : List (Amb m) :=
  (List.range (p + 1)).flatMap fun j =>
    if decide (Even (p - j)) = b then
      List.replicate (p.choose j) (gadgetVec p a χ i j true) ++
        List.replicate (p.choose j) (gadgetVec p a χ i j false)
    else []

/-- Alice's prefix `⊎_{i ∈ [N]} G_{z_i}(a_i)` (§8.5). -/
noncomputable def alicePrefix {N m : ℕ} (p : ℕ) (a : Fin N → EuclideanSpace ℝ (Fin m))
    (χ : Fin N → Fin m) (z : Fin N → Bool) : List (Amb m) :=
  (List.finRange N).flatMap fun i => gadget p a χ (z i) i

/-- The number of copies `L = ⌊m^{(p−2)/2}⌋` of each suffix vector. -/
noncomputable def suffixCopies (p m : ℕ) : ℕ :=
  ⌊(m : ℝ) ^ (((p : ℝ) - 2) / 2)⌋₊

/-- The query amplitude `Q = L √m`. -/
noncomputable def queryAmp (p m : ℕ) : ℝ := (suffixCopies p m : ℝ) * Real.sqrt m

/-- Bob's vector `v_ℓ = (1/√m) a_q + √(1 − 1/m) w_ℓ`. -/
noncomputable def bobVec {N m : ℕ} (a : Fin N → EuclideanSpace ℝ (Fin m)) (q : Fin N)
    (ℓ : Fin m) : Amb m :=
  (1 / Real.sqrt m) • codeVec (a q) + Real.sqrt (1 - 1 / (m : ℝ)) • sufVec ℓ

/-- Bob's suffix: `L` copies of `v_1`, then `L` copies of `v_2`, …, `L` copies of `v_m`. -/
noncomputable def bobSuffix {N m : ℕ} (p : ℕ) (a : Fin N → EuclideanSpace ℝ (Fin m)) (q : Fin N) :
    List (Amb m) :=
  (List.finRange m).flatMap fun ℓ => List.replicate (suffixCopies p m) (bobVec a q ℓ)

/-- The hard stream `P(z, q)` of (34): Alice's prefix followed by Bob's suffix. -/
noncomputable def hardStream {N m : ℕ} (p : ℕ) (a : Fin N → EuclideanSpace ℝ (Fin m))
    (χ : Fin N → Fin m) (z : Fin N → Bool) (q : Fin N) : List (Amb m) :=
  alicePrefix p a χ z ++ bobSuffix p a q

/-- `κ_p = 2 p! h^p` (Lemma 8.6). -/
noncomputable def kappa (p : ℕ) : ℝ := 2 * (p.factorial : ℝ) * hstep p ^ p

/-- `γ_p = 2 Σ_{j ∈ J₊} c_j t_j` ((29)). -/
noncomputable def gammaP (p : ℕ) : ℝ :=
  2 * ∑ j ∈ (Finset.range (p + 1)).filter (fun j => Even (p - j)), coef p j * level p j

/-- `β_p = 2 λ Σ_{j ∈ J₊} c_j` ((29)). -/
noncomputable def betaP (p : ℕ) : ℝ :=
  2 * lam * ∑ j ∈ (Finset.range (p + 1)).filter (fun j => Even (p - j)), coef p j

/-- The code response `Z_i = ⟨a_i, s⟩` of a vector `s` of the ambient space (Lemma 8.6). -/
noncomputable def codeResp {N m : ℕ} (a : Fin N → EuclideanSpace ℝ (Fin m)) (i : Fin N)
    (s : Amb m) : ℝ :=
  ⟪codeVec (a i), s⟫

/-- The local baseline `B_i = λ ⟨e_{χ(i)}, s⟩` (Lemma 8.6). -/
noncomputable def anchorBase {N m : ℕ} (χ : Fin N → Fin m) (i : Fin N) (s : Amb m) : ℝ :=
  lam * ⟪anchorVec (χ i), s⟫

/-- The global baseline `V_0(q) = M_p(P(0, q))` (§8.6). -/
noncomputable def baseline {N m : ℕ} (p : ℕ) (a : Fin N → EuclideanSpace ℝ (Fin m))
    (χ : Fin N → Fin m) (q : Fin N) : ℝ :=
  moment p (hardStream p a χ (fun _ => false) q)

/-- A balanced coloring: `|χ⁻¹(c)| = N/m` for every color `c` (§8.1). -/
def IsBalanced {N m : ℕ} (χ : Fin N → Fin m) : Prop :=
  ∀ c : Fin m, (Finset.univ.filter (fun i => χ i = c)).card = N / m

/-- Unit codewords with nonnegative coordinates, `a_i ∈ ℝ^m_{≥0}`, `‖a_i‖ = 1` (§8.1). -/
def IsUnitNonnegCode {N m : ℕ} (a : Fin N → EuclideanSpace ℝ (Fin m)) : Prop :=
  ∀ i, ‖a i‖ = 1 ∧ ∀ k, 0 ≤ a i k

/-- `R_i = 1 + Σ_{r ≠ i} ⟨a_i, a_r⟩` (§8.1, (35)). -/
noncomputable def rowSum {N m : ℕ} (a : Fin N → EuclideanSpace ℝ (Fin m)) (i : Fin N) : ℝ :=
  1 + ∑ r ∈ Finset.univ.erase i, ⟪a i, a r⟫

/-- `R_max = (N/m)^{(p−1)/(p−2)}` (§8.1). -/
noncomputable def rMax (p N m : ℕ) : ℝ :=
  ((N : ℝ) / m) ^ (((p : ℝ) - 1) / ((p : ℝ) - 2))

/-- The number of encoded bits `N = m ⌊c_N m^{ρ_p − 1}⌋` (§8.1). -/
noncomputable def codeLength (p : ℕ) (cN : ℝ) (m : ℕ) : ℕ :=
  m * ⌊cN * (m : ℝ) ^ (rho p - 1)⌋₊

/-- The normalized incidence vector `1_S / √|S|` of a subset `S ⊆ [m]` (Lemma 8.2). -/
noncomputable def incUnit {m : ℕ} (S : Finset (Fin m)) : EuclideanSpace ℝ (Fin m) :=
  WithLp.toLp 2 (fun k : Fin m => if k ∈ S then 1 / Real.sqrt (S.card : ℝ) else 0)

end CosDensity


