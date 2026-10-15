-- Prove2me | Definitions.Def_OAI_MathematicalPhysics_PlanarAnderson_Spectrum
-- name    : OAI_MathematicalPhysics_PlanarAnderson_Spectrum
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-14T17:23:43.535519+00:00
-- url     : https://prove2.me/theorems/4844a64a-e2ff-4a68-8770-4e86cf640810
-- title:
--   Nearest-neighbour hopping, bounded potentials and the Anderson operator on $\ell^2(\mathbb{Z}^2)$, with truncated plane waves and constant-potential boxes
-- statement:
--   Throughout, a site is a point $x=(x_1,x_2)$ of the square lattice $\mathbb{Z}^2$, a configuration is a real function $v:\mathbb{Z}^2\to\mathbb{R}$ (a potential), and $\mathcal{H}=\ell^2(\mathbb{Z}^2;\mathbb{C})$ is the Hilbert space of square-summable functions $u:\mathbb{Z}^2\to\mathbb{C}$ with inner product $\langle u,w\rangle=\sum_{x}\overline{u(x)}\,w(x)$. These, together with the disorder law, the Anderson-operator predicate and the target spectral interval, come from the underlying base definitions. For $x\in\mathbb{Z}^2$ let $\delta_x\in\mathcal{H}$ be the indicator function of $\{x\}$, and for integers $a\le b$ write $[a,b]$ for $\{a,a+1,\dots,b\}$ (empty if $a>b$).
--
--   This file introduces the following objects.
--
--   1. **Reindexing isometries.** For a bijection $e:\mathbb{Z}^2\to\mathbb{Z}^2$, the operator $R_e:\mathcal{H}\to\mathcal{H}$, $(R_e u)(x)=u(e(x))$. Since $u\circ e$ is again square-summable with the same norm, $R_e$ is a $\mathbb{C}$-linear isometry.
--
--   2. **Translations.** For $a\in\mathbb{Z}^2$, the bijection $\tau_a:\mathbb{Z}^2\to\mathbb{Z}^2$, $\tau_a(x)=x+a$, with inverse $x\mapsto x-a$. Thus $(R_{\tau_a}u)(x)=u(x+a)$.
--
--   3. **Hopping operator.** The bounded operator $A=R_{\tau_{(1,0)}}+R_{\tau_{(-1,0)}}+R_{\tau_{(0,1)}}+R_{\tau_{(0,-1)}}$ on $\mathcal{H}$, that is,
--
--      $$
--      (Au)(x_1,x_2)=u(x_1+1,x_2)+u(x_1-1,x_2)+u(x_1,x_2+1)+u(x_1,x_2-1),
--      $$
--
--      the sum of the values of $u$ at the four nearest neighbours of $x$ (the adjacency operator of $\mathbb{Z}^2$).
--
--   4. **Potential operator.** For $h\ge 0$ and a configuration $v$ with $|v(x)|\le h$ for every $x\in\mathbb{Z}^2$, the multiplication operator $(V_v u)(x)=v(x)\,u(x)$, a bounded operator on $\mathcal{H}$ of norm at most $h$.
--
--   5. **Anderson operator.** Under the same hypotheses, $H_v=A+V_v$, so that
--
--      $$
--      (H_v u)(x)=u(x_1+1,x_2)+u(x_1-1,x_2)+u(x_1,x_2+1)+u(x_1,x_2-1)+v(x)\,u(x).
--      $$
--
--   6. **Boxes.** For $n\in\mathbb{N}$: the box $Q_n=[0,n]^2$, which has $(n+1)^2$ sites; the enlarged box $Q_n^{+}=[-1,n+1]^2$; the interior box $Q_n^{-}=[1,n-1]^2$, which is empty for $n\le 1$; and the boundary layer $\partial Q_n=Q_n^{+}\setminus Q_n^{-}$.
--
--   7. **Plane waves and their truncations.** For $q\in\mathbb{C}$, the plane wave $\phi_q(x)=q^{x_1+x_2}$ (an integer power of $q$), and for $n\in\mathbb{N}$ its truncation to the box $Q_n$,
--
--      $$
--      \psi_{q,n}=\sum_{x\in Q_n}\phi_q(x)\,\delta_x\in\mathcal{H},\qquad \psi_{q,n}(x)=\begin{cases}q^{x_1+x_2}, & x\in Q_n,\\ 0, & x\notin Q_n.\end{cases}
--      $$
--
--   8. **Free energy.** $E(q)=2\,(q+q^{-1})$ for $q\in\mathbb{C}$. For $q=e^{\mathrm{i}\theta}$ on the unit circle, $E(q)=4\cos\theta$, which ranges over $[-4,4]$.
--
--   9. **Patches and trial sites.** For $n\in\mathbb{N}$ the patch index set is $\{0,\dots,n\}\times\{0,\dots,n\}$. A patch index $p=(i,j)$ is placed at the site $(i,j)\in Q_n$, and for $k\in\mathbb{N}$ its $k$-th trial site is
--
--      $$
--      \sigma_{n,k}(i,j)=\bigl(k(n+1)+i,\ j\bigr)\in\mathbb{Z}^2 .
--      $$
--
--      Thus $\sigma_{n,k}$ places a copy of $Q_n$ at $Q_n+(k(n+1),0)$; the copies for $k=0,1,2,\dots$ lie side by side along the first axis without overlapping.
--
--   10. **Constant boxes.** A configuration $v$ has constant boxes at level $h\in\mathbb{R}$ if for every $w\in(-h,h)$, every $\varepsilon>0$ and every $n\in\mathbb{N}$ there is a translation vector $t\in\mathbb{Z}^2$ such that
--
--       $$
--       |v(y+t)-w|<\varepsilon\qquad\text{for all } y\in Q_n ,
--       $$
--
--       i.e. on some translate of the box $Q_n$ the potential is uniformly $\varepsilon$-close to the constant $w$.
--
--   These are the objects used to identify the spectrum of the planar Anderson model $H_v$ when the values $v(x)$ are independent and uniform on $[-h,h]$. The hopping operator has norm at most $4$ and the potential at most $h$, which confines the spectrum to $[-4-h,4+h]$. In the other direction, for $|q|=1$ the plane wave satisfies $A\phi_q=E(q)\,\phi_q$ pointwise, so the truncations $\psi_{q,n}$ are approximate eigenvectors of $A$ whose error lives on the boundary layer $\partial Q_n$; moved into a box where $v$ is nearly constant equal to $w$, they become approximate eigenvectors of $H_v$ for the value $E(q)+w$. The trial sites supply infinitely many disjoint copies of $Q_n$, on which an independent potential takes independent values; this is how one shows that almost every configuration has constant boxes.
--
--   **Formalization Note** The Hilbert space is `lp (fun _ : ℤ × ℤ => ℂ) 2`. The objects above are `permute e` (item 1, a linear isometry; `mem_reindex` is the lemma that $u\circ e$ is again in $\ell^2$), `translation a` (item 2, an `Equiv`), `hopping`, `potential v hh hv` and `anderson v hh hv` (items 3 to 5), `cube`, `outerCube`, `innerCube` and `boundary` (item 6, finite sets of sites), `plane` and `cutWave` (item 7), `freeEnergy` (item 8), `Patch n = Fin (n+1) × Fin (n+1)` with `patchSite` and `trialSite` (item 9), and `HasConstantBoxes v h` (item 10, where the box $Q_n$ is quantified through patch indices). The potential and Anderson operators take the proofs `hh : 0 ≤ h` and `hv : ∀ x, |v x| ≤ h` as arguments, because $V_v$ is built with `lp.mapCLM` from the uniformly bounded family of scalar multiplications by $v(x)$. The plane wave uses the integer power `zpow` and the inverse in `freeEnergy` follows Lean's convention $0^{-1}=0$, so for $q=0$ one gets $\phi_0(x)=1$ if $x_1+x_2=0$ and $\phi_0(x)=0$ otherwise, and $E(0)=0$; only $|q|=1$ matters for the spectral argument. The simp lemmas `permute_apply`, `translation_apply`, `hopping_apply`, `potential_apply` and `cutWave_apply` record the pointwise formulas above, and an instance records that $\mathcal{H}$ is nontrivial.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/PlanarAnderson/Spectrum.lean

-- Generated from openai/math@1581d4c lean/OAI/MathematicalPhysics/PlanarAnderson/Spectrum.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the PlanarAndersonSpectrum mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_PlanarAndersonSpectrum

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-! The nearest-neighbor Anderson operator on the square lattice and its almost-sure spectral interval. -/

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace PlanarAnderson
instance : Nontrivial Hilbert := by
  refine ⟨⟨lp.single 2 (0, 0) (1 : ℂ), 0, ?_⟩⟩
  intro he
  have h := congrArg (fun u : Hilbert => u (0, 0)) he
  simp at h

 theorem mem_reindex (e : Site ≃ Site) (u : Hilbert) :
    Memℓp (fun x => u (e x)) 2 := by
  apply memℓp_gen
  exact e.summable_iff.mpr ((lp.memℓp u).summable (by norm_num))

def permute (e : Site ≃ Site) : Hilbert →ₗᵢ[ℂ] Hilbert where
  toFun u := ⟨fun x => u (e x), mem_reindex e u⟩
  map_add' u v := by ext; rfl
  map_smul' c u := by ext; rfl
  norm_map' u := by
    rw [lp.norm_eq_tsum_rpow (by norm_num), lp.norm_eq_tsum_rpow (by norm_num)]
    congr 1
    exact e.tsum_eq (fun x => ‖u x‖ ^ (2 : ℝ≥0∞).toReal)

@[simp] theorem permute_apply (e : Site ≃ Site) (u : Hilbert) (x : Site) :
    permute e u x = u (e x) := rfl

def translation (a : Site) : Site ≃ Site where
  toFun x := x + a
  invFun x := x - a
  left_inv x := add_sub_cancel_right x a
  right_inv x := sub_add_cancel x a

@[simp] theorem translation_apply (a x : Site) : translation a x = x + a := rfl

 def hopping : Hilbert →L[ℂ] Hilbert :=
   (permute (translation (1, 0))).toContinuousLinearMap +
   (permute (translation (-1, 0))).toContinuousLinearMap +
   (permute (translation (0, 1))).toContinuousLinearMap +
   (permute (translation (0, -1))).toContinuousLinearMap

@[simp] theorem hopping_apply (u : Hilbert) (x : Site) :
    hopping u x = u (x.1 + 1, x.2) + u (x.1 - 1, x.2) +
      u (x.1, x.2 + 1) + u (x.1, x.2 - 1) := by
  simp [hopping, translation, sub_eq_add_neg, Prod.add_def]

 def potential (v : Configuration) {h : ℝ} (hh : 0 ≤ h) (hv : ∀ x, |v x| ≤ h) :
    Hilbert →L[ℂ] Hilbert :=
   lp.mapCLM 2 (fun x => (v x : ℂ) • ContinuousLinearMap.id ℂ ℂ) hh
     (fun x => by simpa only [norm_smul, ContinuousLinearMap.norm_id, mul_one,
       Complex.norm_real, Real.norm_eq_abs] using hv x)

@[simp] theorem potential_apply (v : Configuration) {h : ℝ} (hh : 0 ≤ h)
    (hv : ∀ x, |v x| ≤ h) (u : Hilbert) (x : Site) :
    potential v hh hv u x = (v x : ℂ) * u x := rfl

 def anderson (v : Configuration) {h : ℝ} (hh : 0 ≤ h) (hv : ∀ x, |v x| ≤ h) :
    Hilbert →L[ℂ] Hilbert := hopping + potential v hh hv

def cube (n : ℕ) : Finset Site := Finset.Icc 0 (n : ℤ) ×ˢ Finset.Icc 0 (n : ℤ)
def outerCube (n : ℕ) : Finset Site :=
  Finset.Icc (-1) ((n : ℤ) + 1) ×ˢ Finset.Icc (-1) ((n : ℤ) + 1)
def innerCube (n : ℕ) : Finset Site :=
  Finset.Icc 1 ((n : ℤ) - 1) ×ˢ Finset.Icc 1 ((n : ℤ) - 1)
def boundary (n : ℕ) : Finset Site := outerCube n \ innerCube n

def plane (q : ℂ) (x : Site) : ℂ := q ^ (x.1 + x.2)
def cutWave (q : ℂ) (n : ℕ) : Hilbert :=
  ∑ x ∈ cube n, lp.single 2 x (plane q x)
def freeEnergy (q : ℂ) : ℂ := 2 * (q + q⁻¹)

@[simp] theorem cutWave_apply (q : ℂ) (n : ℕ) (x : Site) :
    cutWave q n x = if x ∈ cube n then plane q x else 0 := by
  simp only [cutWave, lp.coeFn_sum, Finset.sum_apply, lp.coeFn_single,
    Finset.sum_pi_single]

abbrev Patch (n : ℕ) := Fin (n + 1) × Fin (n + 1)

def patchSite (n : ℕ) (p : Patch n) : Site := ((p.1.val : ℤ), (p.2.val : ℤ))
def trialSite (n : ℕ) (k : ℕ) (p : Patch n) : Site :=
  (((k * (n + 1) + p.1.val : ℕ) : ℤ), (p.2.val : ℤ))

def HasConstantBoxes (v : Configuration) (h : ℝ) : Prop :=
  ∀ w ∈ Set.Ioo (-h) h, ∀ ε : ℝ, 0 < ε → ∀ n : ℕ,
    ∃ t : Site, ∀ p : Patch n, |v (patchSite n p + t) - w| < ε

end PlanarAnderson

end

end OAI


