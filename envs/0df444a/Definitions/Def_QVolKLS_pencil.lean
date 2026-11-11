-- Prove2me | Definitions.Def_QVolKLS_pencil
-- name    : QVolKLS_pencil
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:38:35.231944+00:00
-- url     : https://prove2.me/theorems/777ea0cb-a75c-4c2a-9b82-050b57281a0d
-- title:
--   The pencil $K_0$, the cone $C$, the cooling schedule (54), $Z(a)$, $Z_\Lambda(a)$, $\pi_i$, $\nu_\Lambda$, $q_{\mathrm{in}}$, $q_{\mathrm{out}}$
-- statement:
--   Fix $d\ge1$, $D=d+1$, a body $K\subseteq\mathbb R^d$ and $\kappa>0$ (after rescaling, $B(0,1)\subseteq K\subseteq B(0,\kappa)$). Points of $\mathbb R^D$ are $(x_0,x')$.
--
--   1. The **pencil** (45) is $K_0=\{(x_0,x'):0\le x_0\le2\kappa,\ x'\in K,\ \|x'\|_2\le x_0\}$ and the truncated **cone** is $C=\{(x_0,x'):0\le x_0\le2\kappa,\ \|x'\|_2\le x_0\}$.
--   2. The **schedule** (54) is $a_0=4D$, $a_{i+1}=\big(1-\frac1{16\lceil\sqrt d\rceil}\big)a_i$, $m=\min\{i:a_i\kappa\le1\}$, and $\Delta=a_i/(16\lceil\sqrt d\rceil)=a_i-a_{i+1}$.
--   3. The continuous laws are $Z(a)=\int_{K_0}e^{-ax_0}\,dx$ and $\pi_a(dx)=Z(a)^{-1}e^{-ax_0}1_{K_0}(x)\,dx$; the continuous relative second moment of $\pi_{a'}$ with respect to $\pi_a$ is $\mathbb E_{\pi_a}[(\pi_{a'}/\pi_a)^2]$.
--   4. On the lattice $\Lambda=h\mathbb Z^D$: $Z_\Lambda(a)=h^D\sum_{z\in K_0\cap h\mathbb Z^D}e^{-az_0}$, $\pi_i(z)=h^De^{-a_iz_0}/Z_\Lambda(a_i)$ (47), and the finite relative second moment is $\sum_z\pi'(z)^2/\pi(z)$.
--   5. On the cone (49): $Z_{C,\Lambda}=h^D\sum_{z\in C\cap h\mathbb Z^D}e^{-a_0z_0}$ and $\nu_\Lambda(z)=h^De^{-a_0z_0}/Z_{C,\Lambda}$.
--   6. The endpoint probabilities (50) are $q_{\mathrm{in}}=\Pr_{z\sim\nu_\Lambda}[z'\in K]$ and $q_{\mathrm{out}}=\Pr_{z\sim\pi_m}[z_0\in[\kappa,2\kappa]]$.
--
--   A lattice law placed on a point register of format $(b,p)$ (with $h=2^{-p}$) gives each register string the weight of the point it encodes, and zero to strings outside the support.
--
--   These are the objects of the volume identity (51) and of Lemmas 6.2–6.3.
--
--   **Formalization Note** `pencil`, `cone`, `coolingRatio`, `coolingA`, `coolingLength` (an `sInf` in `ℕ`; nonempty for $d\ge1$), `coolingDelta`, `pencilZ`, `pencilDensity`, `contRelMoment`, `latSum`, `pencilZLat`, `pencilLatLaw`, `finRelMoment`, `coneZLat`, `coneLatLaw`, `qIn`, `qOut`, `regWeight`. Lattice sums are `tsum`s over bounded sets, hence finite sums.
-- source:
--   R. Zhang, Improved Upper and Lower Bounds for Quantum Convex-Body Volume Estimation, arXiv:2610.04987 (preprint, held version, sha256 eee7a45e7117af08035a8d75fd6f145fa82ddade51ad87a6507911b6a0aa4f80), §6.1–§6.2, pp.44–46, (45), (47), (49), (50), (54)

import Definitions.Def_QVolKLS_memOracle

set_option autoImplicit false

namespace QVolKLS

open MeasureTheory

/-!
# The pencil, the cone, the cooling schedule, and their lattice laws

R. Zhang, *Improved Upper and Lower Bounds for Quantum Convex-Body Volume Estimation*,
arXiv:2610.04987 (held version, sha256 eee7a45e…), §6.1–§6.2, pp.44–47: after rescaling,
`B(0, 1) ⊆ K ⊆ B(0, κ)` in `ℝ^d` and `D = d + 1`;
* (45) the pencil `K₀ = {(x₀, x′) : 0 ≤ x₀ ≤ 2κ, x′ ∈ K, ‖x′‖₂ ≤ x₀}`;
* p.45 `Z(a) = ∫_{K₀} e^{−a x₀} dx` and `π_a(dx) = Z(a)^{−1} e^{−a x₀} 1_{K₀}(x) dx`;
* (47) `Z_Λ(a) = h^D Σ_{z ∈ K₀ ∩ hℤ^D} e^{−a z₀}` and `π_i(z) = h^D e^{−a_i z₀}/Z_Λ(a_i)`;
* (49) the cone `C = {(x₀, x′) : 0 ≤ x₀ ≤ 2κ, ‖x′‖₂ ≤ x₀}`, `Z_{C,Λ} = h^D Σ_{z ∈ C ∩ hℤ^D} e^{−a₀z₀}`,
  `ν_Λ(z) = h^D e^{−a₀z₀}/Z_{C,Λ}`;
* (50) `q_in = Pr_{z∼ν_Λ}[z′ ∈ K]`, `q_out = Pr_{z∼π_m}[z₀ ∈ [κ, 2κ]]`;
* (54) the schedule `a₀ = 4D`, `a_{i+1} = (1 − 1/(16⌈√d⌉)) a_i`, `m = min{i : a_i κ ≤ 1}`.

**Formalization Note.**
* A point of `ℝ^D` is `(x₀, x′)` with `x₀ = x 0` and `x′ = tailE x`. `Z(a)` is a Bochner integral over
  `K₀`; for a convex body `K` the integrand is bounded and `K₀` is compact, so it is integrable.
* Relative second moments are written from their definition: `E_{π_a}[(π_{a′}/π_a)²] = ∫_{K₀} p_{a′}²/p_a dx`
  with the densities `p_a = e^{−a x₀}/Z(a)` on `K₀`, and `Σ_{z ∈ K₀ ∩ hℤ^D} π′(z)²/π(z)` for lattice laws.
* Lattice sums `latSum S h f = Σ_{z ∈ S ∩ hℤ^D} f(z)` are `tsum`s over the integer vectors `k` with
  `hk ∈ S`; every set summed over here is bounded, so these are finite sums.
* `coolingLength d κ` is `m = min{i : a_i κ ≤ 1}` (an `sInf` in `ℕ`; the set is nonempty for
  `d ≥ 1`, since then `0 < 1 − 1/(16⌈√d⌉) < 1`). `coolingDelta d i = a_i/(16⌈√d⌉) = a_i − a_{i+1}`.
* `regWeight D b p S f` is the weight `f` restricted to `S`, read on the point register of format
  `(b, p)` (`decodePoint`): it is the law `f` on `S ∩ 2^{-p}ℤ^D` placed on register labels, and zero
  on labels outside `S`.
-/

/-- Zhang, (45): the **pencil** `K₀ = {(x₀, x′) : 0 ≤ x₀ ≤ 2κ, x′ ∈ K, ‖x′‖₂ ≤ x₀}`. -/
def pencil {d : ℕ} (K : Set (Euc d)) (κ : ℝ) : Set (Euc (d + 1)) :=
  {x | 0 ≤ x 0 ∧ x 0 ≤ 2 * κ ∧ tailE x ∈ K ∧ ‖tailE x‖ ≤ x 0}

/-- Zhang, p.45: the truncated round **cone** `C = {(x₀, x′) : 0 ≤ x₀ ≤ 2κ, ‖x′‖₂ ≤ x₀}`. -/
def cone (d : ℕ) (κ : ℝ) : Set (Euc (d + 1)) :=
  {x | 0 ≤ x 0 ∧ x 0 ≤ 2 * κ ∧ ‖tailE x‖ ≤ x 0}

/-- Zhang, (54): the cooling factor `1 − 1/(16⌈√d⌉)`. -/
noncomputable def coolingRatio (d : ℕ) : ℝ :=
  1 - 1 / (16 * (Nat.ceil (Real.sqrt d) : ℝ))

/-- Zhang, (54): the schedule `a_i = 4D (1 − 1/(16⌈√d⌉))^i`, `D = d + 1`. -/
noncomputable def coolingA (d i : ℕ) : ℝ :=
  4 * ((d : ℝ) + 1) * coolingRatio d ^ i

/-- Zhang, (54): the number of stages `m = min{i : a_i κ ≤ 1}`. -/
noncomputable def coolingLength (d : ℕ) (κ : ℝ) : ℕ :=
  sInf {i : ℕ | coolingA d i * κ ≤ 1}

/-- Zhang, p.46: `∆ = a_i/(16⌈√d⌉)` at stage `i` (so `a_{i+1} = a_i − ∆`). -/
noncomputable def coolingDelta (d i : ℕ) : ℝ :=
  coolingA d i / (16 * (Nat.ceil (Real.sqrt d) : ℝ))

/-- Zhang, p.45: `Z(a) = ∫_{K₀} e^{−a x₀} dx`. -/
noncomputable def pencilZ {d : ℕ} (K : Set (Euc d)) (κ a : ℝ) : ℝ :=
  ∫ x in pencil K κ, Real.exp (-a * x 0)

/-- Zhang, p.45: the density `e^{−a x₀}/Z(a)` of `π_a` on `K₀`. -/
noncomputable def pencilDensity {d : ℕ} (K : Set (Euc d)) (κ a : ℝ) (x : Euc (d + 1)) : ℝ :=
  Real.exp (-a * x 0) / pencilZ K κ a

/-- Zhang, Lemma 6.2, p.46: the continuous relative second moment
`E_{π_a}[(π_{a′}/π_a)²] = ∫_{K₀} p_{a′}(x)²/p_a(x) dx`. -/
noncomputable def contRelMoment {d : ℕ} (K : Set (Euc d)) (κ a a' : ℝ) : ℝ :=
  ∫ x in pencil K κ, pencilDensity K κ a' x ^ 2 / pencilDensity K κ a x

/-- The lattice sum `Σ_{z ∈ S ∩ hℤ^D} f(z)`. -/
noncomputable def latSum {D : ℕ} (S : Set (Euc D)) (h : ℝ) (f : Euc D → ℝ) : ℝ :=
  ∑' k : {k : Fin D → ℤ // latticePt h k ∈ S}, f (latticePt h k.1)

/-- Zhang, (47): `Z_Λ(a) = h^D Σ_{z ∈ K₀ ∩ hℤ^D} e^{−a z₀}`. -/
noncomputable def pencilZLat {d : ℕ} (K : Set (Euc d)) (κ h a : ℝ) : ℝ :=
  h ^ (d + 1) * latSum (pencil K κ) h (fun z => Real.exp (-a * z 0))

/-- Zhang, (47): the lattice law `h^D e^{−a z₀}/Z_Λ(a)` on `K₀ ∩ hℤ^D` (`π_i` is `a = a_i`). -/
noncomputable def pencilLatLaw {d : ℕ} (K : Set (Euc d)) (κ h a : ℝ) (z : Euc (d + 1)) : ℝ :=
  h ^ (d + 1) * Real.exp (-a * z 0) / pencilZLat K κ h a

/-- Zhang, Lemma 6.2, p.46: the finite relative second moment
`E_{π}[(π′/π)²] = Σ_{z ∈ K₀ ∩ hℤ^D} π′(z)²/π(z)` of the lattice laws at `a` (`π`) and `a′` (`π′`). -/
noncomputable def finRelMoment {d : ℕ} (K : Set (Euc d)) (κ h a a' : ℝ) : ℝ :=
  latSum (pencil K κ) h (fun z => pencilLatLaw K κ h a' z ^ 2 / pencilLatLaw K κ h a z)

/-- Zhang, (49): `Z_{C,Λ} = h^D Σ_{z ∈ C ∩ hℤ^D} e^{−a₀ z₀}` with `a₀ = 4D`. -/
noncomputable def coneZLat (d : ℕ) (κ h : ℝ) : ℝ :=
  h ^ (d + 1) * latSum (cone d κ) h (fun z => Real.exp (-coolingA d 0 * z 0))

/-- Zhang, (49): the cone law `ν_Λ(z) = h^D e^{−a₀ z₀}/Z_{C,Λ}` on `C ∩ hℤ^D`. -/
noncomputable def coneLatLaw (d : ℕ) (κ h : ℝ) (z : Euc (d + 1)) : ℝ :=
  h ^ (d + 1) * Real.exp (-coolingA d 0 * z 0) / coneZLat d κ h

/-- Zhang, (50): `q_in = Pr_{z∼ν_Λ}[z′ ∈ K]`. -/
noncomputable def qIn {d : ℕ} (K : Set (Euc d)) (κ h : ℝ) : ℝ :=
  latSum (cone d κ ∩ {z | tailE z ∈ K}) h (coneLatLaw d κ h)

/-- Zhang, (50): `q_out = Pr_{z∼π_m}[z₀ ∈ [κ, 2κ]]`, `π_m` the lattice law at `a_m`. -/
noncomputable def qOut {d : ℕ} (K : Set (Euc d)) (κ h : ℝ) : ℝ :=
  latSum (pencil K κ ∩ {z | κ ≤ z 0 ∧ z 0 ≤ 2 * κ}) h
    (pencilLatLaw K κ h (coolingA d (coolingLength d κ)))

/-- A weight `f` on the set `S ⊆ ℝ^D`, read on the point register of format `(b, p)`: label `z`
gets `f(decodePoint z)` if `decodePoint z ∈ S`, and `0` otherwise. -/
noncomputable def regWeight (D b p : ℕ) (S : Set (Euc D)) (f : Euc D → ℝ) :
    QAlgorithms.Qubits (D * b) → ℝ :=
  fun z => S.indicator f (decodePoint D b p z)

end QVolKLS


