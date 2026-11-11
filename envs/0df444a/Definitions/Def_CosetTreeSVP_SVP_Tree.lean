-- Prove2me | Definitions.Def_CosetTreeSVP_SVP_Tree
-- name    : CosetTreeSVP_SVP_Tree
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T06:32:35.737403+00:00
-- url     : https://prove2.me/theorems/15519516-b739-4757-aea6-576f66565f82
-- title:
--   Coordinate blocks H_j, the difference tree Y_{j,a}, C_δ, k*, θ*, α*, k_{α,θ,r}, the target A_δ(θ), the estimator Â_δ(θ), K_j, σ_j, and the probabilities over U, δ and the samples
-- statement:
--   Let $q$ be prime, $p$ a power of two and $m = \log_2 p + 1$ (the parameters of Eq. (17) in the lemmas).
--
--   **Coordinate decomposition (§4.2, footnote 7).** With $\ell = \lfloor n/m\rfloor$, block $j \in \{1,\dots,m-1\}$ consists of the coordinates $(j-1)\ell+1,\dots,j\ell$ and block $m$ of the remaining coordinates $(m-1)\ell+1,\dots,n$; $H_j \subseteq \mathbb F_q^n$ is the set of vectors vanishing outside block $j$, so $\mathbb F_q^n = H_1\oplus\cdots\oplus H_m$ and $(Y)_{H_j}$ is the block-$j$ component of $Y$. (When $m \mid n$ this is the main text's decomposition into blocks of $n/m$ coordinates.) $P_j = H_1\oplus\cdots\oplus H_j$, $P_0 = \{0\}$.
--
--   **Difference tree (Eqs. (21), (25)).** For leaves $Y_{0,r}$, $r \in [0,p)$, set $Y_{j,a} = Y_{j-1,2a} - Y_{j-1,2a+1}$ for $j \in [m-1]$, $a \in [0,p/2^j)$. A family $\delta = (\delta_{j,a})$ has $\delta_{j,a} \in H_j$, and
--   $$C_\delta = \prod_{j=1}^{m-1}\prod_{a=0}^{p/2^j-1}\mathbf 1\{(Y_{j,a})_{H_j} = \delta_{j,a}\}.$$
--   With $\varepsilon_r = (-1)^{\mathrm{wt}_2(r)}$, $U \in GL_n(\mathbb F_q)$ and $w \in \mathbb F_q^n$: $k^* = U^{-T}w$, $\theta^* = (k^*)_{H_m}$, $\alpha^*_{j,a} = \varepsilon_{a2^j}(k^*)_{H_j}$ (Eq. (22)), and for $\alpha = (\alpha_{j,a})$, $\theta \in H_m$ the coefficients of Eq. (28) are
--   $$k_{\alpha,\theta,r} = \varepsilon_r\theta + \sum_{j=1}^{m-1}\varepsilon_{r \bmod 2^j}\,\alpha_{j,\lfloor r/2^j\rfloor},$$
--   the unique vectors with $\langle\theta, Y_{m-1,0}\rangle + \sum_{j,a}\langle\alpha_{j,a},Y_{j,a}\rangle = \sum_r\langle k_{\alpha,\theta,r},Y_{0,r}\rangle$, since $Y_{j,a} = \sum_{b<2^j}\varepsilon_bY_{0,a2^j+b}$.
--
--   **Target and estimator (Eqs. (27), (33)).** For independent $X_0,\dots,X_{p-1}\sim D_{L^*,s}$ and leaves $Y_{0,r} = U[X_r]_q$,
--   $$A_\delta(\theta) = Q^{p-1}\,\mathbb E\big[C_\delta(X_0,\dots,X_{p-1})\,2\pi i X_0\,\omega_q^{\langle\theta,(Y_{m-1,0})_{H_m}\rangle}\ \big|\ U,\delta\big].$$
--   From sample lists $X_{r,i}$, $r \in [0,p)$, $i \in [N]$, with $Y_{0,r}(i) = U[X_{r,i_r}]_q$,
--   $$\hat A_\delta(\theta) = \frac{Q^{p-1}}{N^p}\sum_{i\in[N]^p}C_\delta(i)\,2\pi iX_{0,i_0}\,\omega_q^{\langle\theta,(Y_{m-1,0}(i))_{H_m}\rangle}.$$
--
--   **$K_j$, $\sigma_j$ (Eq. (38)).** $K_j = \{Bx : x \in \mathbb Z^n,\ x \bmod q \in U^TP_j\}$ and $\sigma_j = q/(2^{j/2}s)$.
--
--   **Probabilities.** $U$ is uniform on $GL_n(\mathbb F_q)$, $\delta$ uniform on $\prod_{j,a}H_j$, the samples are independent $D_{L^*,s}$; $\Pr_U$, $\Pr_\delta$, $\Pr_{U,\delta}$, $\mathbb E_{\delta,X}[\,\cdot \mid U]$ and $\Pr_{U,\delta,X}$ are the corresponding averages and sums in $[0,\infty]$.
--
--   **Formalization Note.** `blk`, `InH`, `compH`, `InP`, `Hsub`, `TIdx` (node $(j,a)$ stored with $j-1$), `Fam`, `epsR`, `Ytree`, `Cdelta`, `leaves`, `first`, `kStar`, `thetaStar`, `alphaStar`, `kCoef`, `Adelta Q B s U δ θ`, `Ahat Q B U δ X θ`, `Kj`, `sigmaJ`, `prU`, `prDelta`, `prUDelta`, `sampleW`, `expDeltaX`, `prUDeltaX`. $x \bmod q \in U^TP_j$ is written $U^{-T}(x \bmod q) \in P_j$. $A_\delta$ is an unconditional sum over $(L^*)^p$, which converges absolutely for a nonsingular $B$.
-- source:
--   Hhan, Finding a Shortest Vector and More in 2^{n/2+o(n)} Time using q-ary Coset Difference Tree, arXiv:2609.02764 (held version, sha256 687602f4…), pp. 16–19 (PDF 18–21), §4.2–4.3, Eqs. (21)–(28), (32), (33), footnote 7; p. 23 (PDF 25), Eq. (38)

import Mathlib
import Definitions.Def_SuperlatSVP_lat
import Definitions.Def_RegevLWE_GaussConv_Lattice
import Definitions.Def_RegevLWE_Hyperplane_DiscreteGaussian
import Definitions.Def_CosetTreeSVP_SVP_Basics

open MeasureTheory
open scoped ENNReal

namespace CosetTreeSVP.SVP

/-! ### Coordinate decomposition `F_qⁿ = H₁ ⊕ ⋯ ⊕ H_m` (§4.2 and footnote 7) -/

/-- The block (`1, …, m`) of the coordinate `k ∈ {0, …, n−1}`: with `ℓ = ⌊n/m⌋`, blocks
`1, …, m−1` hold `ℓ` consecutive coordinates each and block `m` holds the remaining
`n − (m−1)ℓ` (footnote 7; for `m ∣ n` every block has `n/m` coordinates, as in the main text). -/
def blk (n m : ℕ) (k : Fin n) : ℕ := min (k.val / (n / m)) (m - 1) + 1

/-- `y ∈ H_j`: `y` vanishes outside block `j`. -/
def InH {n q : ℕ} (m j : ℕ) (y : Fin n → ZMod q) : Prop := ∀ k, blk n m k ≠ j → y k = 0

/-- The component `(Y)_{H_j}` of `Y ∈ F_qⁿ`. -/
def compH {n q : ℕ} (m j : ℕ) (Y : Fin n → ZMod q) : Fin n → ZMod q :=
  fun k => if blk n m k = j then Y k else 0

/-- `y ∈ P_j = H₁ ⊕ ⋯ ⊕ H_j` (Eq. (38); `P₀ = {0}`). -/
def InP {n q : ℕ} (m j : ℕ) (y : Fin n → ZMod q) : Prop := ∀ k, j < blk n m k → y k = 0

instance {n q : ℕ} (m j : ℕ) : DecidablePred (InH (n := n) (q := q) m j) :=
  fun y => by unfold InH; infer_instance

/-- `H_j` as a finite type. -/
abbrev Hsub (n m q j : ℕ) := {y : Fin n → ZMod q // InH m j y}

instance {n m q j : ℕ} : Nonempty (Hsub n m q j) := ⟨⟨0, fun _ _ => rfl⟩⟩

/-- The index set of the tree nodes `(j, a)`, `j ∈ [m−1]`, `a ∈ [0, p/2^j)`; the level of
`⟨j', a⟩` is `j = j' + 1`. -/
abbrev TIdx (p m : ℕ) := Σ j : Fin (m - 1), Fin (p / 2 ^ (j.val + 1))

/-- The level `j ∈ [m−1]` of a tree node. -/
def TIdx.lvl {p m : ℕ} (ia : TIdx p m) : ℕ := ia.1.val + 1

/-- A family `(δ_{j,a})` (or `(α_{j,a})`) with `δ_{j,a} ∈ H_j`. -/
abbrev Fam (n p m q : ℕ) := (ia : TIdx p m) → Hsub n m q (ia.1.val + 1)

/-- The underlying vectors of a family. -/
def Fam.val {n p m q : ℕ} (δ : Fam n p m q) : TIdx p m → Fin n → ZMod q := fun ia => (δ ia).val

/-! ### The difference tree (Eqs. (21)–(28)) -/

/-- `ε_r := (−1)^{wt₂(r)}`, `wt₂` the binary Hamming weight. -/
def epsR (r : ℕ) : ℤ := (-1) ^ (Nat.digits 2 r).sum

/-- The tree `Y_{0,a} := Y0 a`, `Y_{j,a} := Y_{j−1,2a} − Y_{j−1,2a+1}`. -/
def Ytree {n q : ℕ} (Y0 : ℕ → Fin n → ZMod q) : ℕ → ℕ → Fin n → ZMod q
  | 0, a => Y0 a
  | j + 1, a => Ytree Y0 j (2 * a) - Ytree Y0 j (2 * a + 1)

/-- `C_δ = ∏_{j ∈ [m−1]} ∏_{a ∈ [0,p/2^j)} 1{(Y_{j,a})_{H_j} = δ_{j,a}}` (Eq. (25)), for the
leaves `Y_{0,r} = Y0 r`. -/
noncomputable def Cdelta {n p m q : ℕ} (δ : Fam n p m q) (Y0 : ℕ → Fin n → ZMod q) : ℝ := by
  classical
  exact ∏ ia : TIdx p m, if compH m ia.lvl (Ytree Y0 ia.lvl ia.2.val) = (δ ia).val then 1 else 0

/-- The leaves `Y_{0,r} = U[X_r]_q` of samples `X₀, …, X_{p−1}` (Eq. (21)); `0` for `r ≥ p`. -/
noncomputable def leaves {n p q : ℕ} (B : Matrix (Fin n) (Fin n) ℝ)
    (U : Matrix.GeneralLinearGroup (Fin n) (ZMod q)) (X : Fin p → E n) : ℕ → Fin n → ZMod q :=
  fun r => if h : r < p then (U : Matrix (Fin n) (Fin n) (ZMod q)).mulVec (resid B q (X ⟨r, h⟩))
    else 0

/-- `X₀` (the first sample), `0` if `p = 0`. -/
noncomputable def first {n p : ℕ} (X : Fin p → E n) : E n := if h : 0 < p then X ⟨0, h⟩ else 0

/-- `k* = U^{−T} w` (Eq. (22)). -/
def kStar {n q : ℕ} (U : Matrix.GeneralLinearGroup (Fin n) (ZMod q)) (w : Fin n → ZMod q) :
    Fin n → ZMod q :=
  ((U⁻¹ : Matrix.GeneralLinearGroup (Fin n) (ZMod q)) : Matrix (Fin n) (Fin n) (ZMod q)).transpose.mulVec w

/-- `θ* = (k*)_{H_m}` (Eq. (22)). -/
def thetaStar {n q : ℕ} (m : ℕ) (U : Matrix.GeneralLinearGroup (Fin n) (ZMod q))
    (w : Fin n → ZMod q) : Fin n → ZMod q :=
  compH m m (kStar U w)

/-- `α*_{j,a} = ε_{a2^j} (k*)_{H_j}` (Eq. (22)), as vectors. -/
def alphaStar {n p m q : ℕ} (U : Matrix.GeneralLinearGroup (Fin n) (ZMod q))
    (w : Fin n → ZMod q) : TIdx p m → Fin n → ZMod q :=
  fun ia => ((epsR (ia.2.val * 2 ^ ia.lvl) : ℤ) : ZMod q) • compH m ia.lvl (kStar U w)

/-- The coefficients `k_{α,θ,r}` of Eq. (28): the unique vectors with
`⟨θ, Y_{m−1,0}⟩ + Σ_{j,a} ⟨α_{j,a}, Y_{j,a}⟩ = Σ_r ⟨k_{α,θ,r}, Y_{0,r}⟩` for all leaves; since
`Y_{j,a} = Σ_{b<2^j} ε_b Y_{0,a2^j+b}` (Eq. (21)),
`k_{α,θ,r} = ε_r θ + Σ_{j=1}^{m−1} ε_{r mod 2^j} α_{j,⌊r/2^j⌋}`. -/
noncomputable def kCoef {n p m q : ℕ} (α : TIdx p m → Fin n → ZMod q) (θ : Fin n → ZMod q)
    (r : ℕ) : Fin n → ZMod q := by
  classical
  exact ((epsR r : ℤ) : ZMod q) • θ +
    ∑ ia : TIdx p m, if r / 2 ^ ia.lvl = ia.2.val then
      ((epsR (r % 2 ^ ia.lvl) : ℤ) : ZMod q) • α ia else 0

/-- The target `A_δ(θ) := Q^{p−1} E[C_δ(X₀, …, X_{p−1}) 2πi X₀ ω_q^{⟨θ,(Y_{m−1,0})_{H_m}⟩} | U, δ]`
(Eq. (27)), the expectation over independent `X₀, …, X_{p−1} ∼ D_{L*,s}`, `L = BZⁿ`, with
`Q = |H₁|` passed as `Q`. -/
noncomputable def Adelta {n p m q : ℕ} (Q : ℕ) (B : Matrix (Fin n) (Fin n) ℝ) (s : ℝ)
    (U : Matrix.GeneralLinearGroup (Fin n) (ZMod q)) (δ : Fam n p m q) (θ : Fin n → ZMod q) :
    CE n :=
  ((Q : ℂ) ^ (p - 1)) •
    ∑' X : Fin p → dualL (SuperlatSVP.lat B),
      ((∏ r, RegevLWE.Hyperplane.discreteGaussian (dualL (SuperlatSVP.lat B)) s (X r) : ℝ) : ℂ) •
        ((Cdelta δ (leaves B U (fun r => (X r : E n))) : ℂ) * (2 * Real.pi * Complex.I) *
          omegaPow q (dotq θ (compH m m
            (Ytree (leaves B U (fun r => (X r : E n))) (m - 1) 0)))) •
        toC (first (fun r => (X r : E n)))

/-- The estimator `Â_δ(θ) := (Q^{p−1}/N^p) Σ_{i∈[N]^p} C_δ(i) 2πi X_{0,i₀} ω_q^{⟨θ,(Y_{m−1,0}(i))_{H_m}⟩}`
(Eqs. (32), (33)) from the sample lists `X_{r,i}`, `r ∈ [0,p)`, `i ∈ [N]`. -/
noncomputable def Ahat {n p m q N : ℕ} (Q : ℕ) (B : Matrix (Fin n) (Fin n) ℝ)
    (U : Matrix.GeneralLinearGroup (Fin n) (ZMod q)) (δ : Fam n p m q)
    (X : Fin p → Fin N → E n) (θ : Fin n → ZMod q) : CE n :=
  (((Q : ℂ) ^ (p - 1)) / ((N : ℂ) ^ p)) •
    ∑ i : Fin p → Fin N,
      ((Cdelta δ (leaves B U (fun r => X r (i r))) : ℂ) * (2 * Real.pi * Complex.I) *
          omegaPow q (dotq θ (compH m m (Ytree (leaves B U (fun r => X r (i r))) (m - 1) 0)))) •
        toC (first (fun r => X r (i r)))

/-! ### The lattices `K_j` and widths `σ_j` (Eq. (38)) -/

/-- `K_j := {Bx : x ∈ Zⁿ, x mod q ∈ S_j}`, `S_j := UᵀP_j`; `x mod q ∈ UᵀP_j` iff
`U^{−T}(x mod q) ∈ P_j`. -/
def Kj {n q : ℕ} (m : ℕ) (B : Matrix (Fin n) (Fin n) ℝ)
    (U : Matrix.GeneralLinearGroup (Fin n) (ZMod q)) (j : ℕ) : Set (E n) :=
  {v | ∃ x : Fin n → ℤ, v = WithLp.toLp 2 (B.mulVec (fun k => (x k : ℝ))) ∧
    InP m j (((U⁻¹ : Matrix.GeneralLinearGroup (Fin n) (ZMod q)) :
      Matrix (Fin n) (Fin n) (ZMod q)).transpose.mulVec (fun k => ((x k : ℤ) : ZMod q)))}

/-- `σ_j := q / (2^{j/2} s)` (Eq. (38)). -/
noncomputable def sigmaJ (q : ℕ) (s : ℝ) (j : ℕ) : ℝ := (q : ℝ) / ((2 : ℝ) ^ ((j : ℝ) / 2) * s)

/-! ### Probabilities over `U`, `δ` and the samples -/

/-- `Pr_U[U ∈ S]` for `U` uniform in `GL_n(F_q)`. -/
noncomputable def prU {n q : ℕ} [NeZero q] (S : Set (Matrix.GeneralLinearGroup (Fin n) (ZMod q))) :
    ℝ≥0∞ :=
  (PMF.uniformOfFintype (Matrix.GeneralLinearGroup (Fin n) (ZMod q))).toOuterMeasure S

/-- `Pr_δ[δ ∈ S]` for independent uniform `δ_{j,a} ∈ H_j`. -/
noncomputable def prDelta {n p m q : ℕ} [NeZero q] (S : Set (Fam n p m q)) : ℝ≥0∞ :=
  (PMF.uniformOfFintype (Fam n p m q)).toOuterMeasure S

/-- `Pr_{U,δ}[(U, δ) ∈ S]`, `U` and `δ` independent and uniform. -/
noncomputable def prUDelta {n p m q : ℕ} [NeZero q]
    (S : Set (Matrix.GeneralLinearGroup (Fin n) (ZMod q) × Fam n p m q)) : ℝ≥0∞ :=
  (PMF.uniformOfFintype (Matrix.GeneralLinearGroup (Fin n) (ZMod q) × Fam n p m q)).toOuterMeasure S

/-- The joint weight of `pN` independent samples `X_{r,i} ∼ D_{M,σ}`. -/
noncomputable def sampleW {n p N : ℕ} (M : Submodule ℤ (E n)) (σ : ℝ) (X : Fin p → Fin N → M) :
    ℝ≥0∞ :=
  ∏ r, ∏ i, dgW M σ (X r i)

/-- `E_{δ,X}[h(δ, X) | U]`: `δ` uniform, `X_{r,i} ∼ D_{L*,s}` independent (`h ≥ 0`). -/
noncomputable def expDeltaX {n p m q N : ℕ} [NeZero q] (B : Matrix (Fin n) (Fin n) ℝ) (s : ℝ)
    (h : Fam n p m q → (Fin p → Fin N → dualL (SuperlatSVP.lat B)) → ℝ≥0∞) : ℝ≥0∞ :=
  ∑ δ : Fam n p m q, (Fintype.card (Fam n p m q) : ℝ≥0∞)⁻¹ *
    ∑' X : Fin p → Fin N → dualL (SuperlatSVP.lat B), sampleW _ s X * h δ X

/-- `Pr_{U,δ,X}[E]`: `U`, `δ` uniform, `X_{r,i} ∼ D_{L*,s}`, all independent. -/
noncomputable def prUDeltaX {n p m q N : ℕ} [NeZero q] (B : Matrix (Fin n) (Fin n) ℝ) (s : ℝ)
    (E : Matrix.GeneralLinearGroup (Fin n) (ZMod q) → Fam n p m q →
      (Fin p → Fin N → dualL (SuperlatSVP.lat B)) → Prop) : ℝ≥0∞ := by
  classical
  exact ∑ U : Matrix.GeneralLinearGroup (Fin n) (ZMod q),
    (Fintype.card (Matrix.GeneralLinearGroup (Fin n) (ZMod q)) : ℝ≥0∞)⁻¹ *
      expDeltaX B s (fun δ X => if E U δ X then 1 else 0)

end CosetTreeSVP.SVP


