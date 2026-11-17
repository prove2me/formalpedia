-- Prove2me | Definitions.Def_LindbladShallow_Supplement_transport
-- name    : LindbladShallow_Supplement_transport
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T14:22:37.096169+00:00
-- url     : https://prove2.me/theorems/2f087aa5-eb2f-4ed8-949d-3c42e94f48d7
-- title:
--   Hard dissipative transport instances $J_x=bS_x$ of Eq. (51) and the radii $\mathcal R_1$, $\mathcal R_{D+1}$
-- statement:
--   The system occupies the cube $[L]^D=\{1,\dots,L\}^D$, $n=L^D$ sites, with two qubits per site. A site holds a vacancy $|v\rangle:=|00\rangle$, a particle in internal state $|0\rangle:=|01\rangle$, or a particle in internal state $|1\rangle:=|10\rangle$; $|11\rangle$ is inert. For an oriented nearest-neighbour bond $x=(s\to t)$,
--   $$
--   S_x:=|v,0\rangle\langle 0,v|+|v,1\rangle\langle 1,v|,\qquad J_x:=bS_x,\qquad \mathcal L:=\sum_x\mathcal D_{J_x},
--   $$
--   so a jump moves the particle from $s$ to $t$ and carries its internal state along.
--
--   The **transport class** consists of the inputs whose sites are the cube (each listed once), whose jump amplitude $b$ is a positive dyadic rational, whose terms are all such bond jumps (so $H=0$), and in which every site belongs to at most two bonds. The rate is $\gamma:=b^2$.
--
--   With $E:=\log(n/\delta)$ (natural logarithm) the two **precision radii** are
--   $$
--   \mathcal R_1(\theta,E):=\theta+\frac{E}{\log(e+E/\theta)},\qquad
--   \mathcal R_{D+1}(\theta,E):=\theta+\Bigl(\frac{E}{\log(e+E/\theta^{D+1})}\Bigr)^{1/(D+1)}.
--   $$
--
--   These are the hard instances and radii of the lower bounds of Theorem 6.1.
--
--   **Formalization Note** The parameters are $D$, $d_0=2$, $\kappa=2$, $r_*=1$, $\mu_*=1$, $d_{\mathrm{inc}}=2$. The instance's own rational $T$ and $\epsilon$ fields are not used: Theorem 6.1 evolves for the real time $T=\theta/\gamma$.
-- source:
--   Shen, Wu, Yuan, Zhang, Shallow Quantum Circuits for Geometrically Local Lindblad Dynamics, arXiv:2610.05362 (held version, sha256 8f4637ef…), §6.1, pp.50–51; §6.2, Eq. (51), p.52

import Mathlib
import Definitions.Def_LindbladShallow_gen
import Definitions.Def_LindbladShallow_Circuit

open scoped Matrix ComplexOrder

namespace LindbladShallow

namespace Supplement

/-- The fixed local parameters of the hard transport instances of §6.2 (arXiv:2610.05362, held
version sha256 8f4637ef…, §6.1–6.2, pp.50–52): dimension `D ≥ 1`, two qubits per site, supports of
two sites (`κ = 2`) at ℓ∞ distance one (`r∗ = 1`), one jump component per term (`µ∗ = 1`), and every
site in at most two bonds (`d_inc = 2`). -/
def transportParams (D : ℕ) (hD : 1 ≤ D) : Params where
  D := D
  d0 := 2
  κ := 2
  rstar := 1
  μstar := 1
  dinc := 2
  hD := hD
  hd0 := by norm_num
  hκ := by norm_num
  hrstar := le_refl 1
  hμstar := le_refl 1
  hdinc := by norm_num

/-- A point of the system cube `[L_side]^D = {1, …, L_side}^D` (§6.1, p.50). -/
def InCube (D L : ℕ) (x : Fin D → ℤ) : Prop := ∀ j, 1 ≤ x j ∧ x j ≤ (L : ℤ)

/-- The two-qubit code of a particle with internal state `a` (§6.2, p.52): `|0⟩ := |01⟩_comp`
(`a = false`) and `|1⟩ := |10⟩_comp` (`a = true`), first component the bit of qubit `0`. The
vacancy is `|v⟩ := |00⟩_comp`, and `|11⟩_comp` is inert. -/
def particleCode (a : Bool) : Bool × Bool := if a then (true, false) else (false, true)

/-- The entry of `S_x := |v,0⟩⟨0,v| + |v,1⟩⟨1,v|` (Eq. (51), p.52) on the ordered support
`[s, t]` of an oriented bond `s → t`: a basis vector of the support is `f (i, k)`, the bit of qubit
`k` at support site `i` (`i = 0` the source `s`, `i = 1` the target `t`). The entry `⟨out|S_x|in⟩`
is `1` exactly when `in` has a particle with internal state `a` at `s` and a vacancy at `t`, and
`out` has the vacancy at `s` and the same particle at `t`. -/
noncomputable def transportEntry (out inn : LocBasis 2 2) : ℚ :=
  open Classical in
  if ∃ a : Bool, (inn (0, 0), inn (0, 1)) = particleCode a ∧ (inn (1, 0), inn (1, 1)) = (false, false) ∧
      (out (0, 0), out (0, 1)) = (false, false) ∧ (out (1, 0), out (1, 1)) = particleCode a
  then 1 else 0

/-- The jump `J_x := b S_x` of an oriented bond with amplitude `b` (Eq. (51), p.52), as a local
matrix with entries in `ℚ + iℚ` on the support `[s, t]` (entry `(q, 0)` means the rational `q`). -/
noncomputable def transportJ (b : ℚ) : QIMat 2 2 :=
  Matrix.of fun out inn => (b * transportEntry out inn, 0)

/-- The class of static rational purely dissipative transport generators "constructed below"
Theorem 6.1 (arXiv:2610.05362, §6.2, Eq. (51), p.52), for side `L_side = L` and jump amplitude `b`:
1. the sites are the cube `[L]^D`, listed without repetition (so `n = L^D`);
2. `b` is a positive dyadic rational, `b = m / 2^k`;
3. every term is a dissipative term with ordered support `[s, t]`, `s, t` in the cube at ℓ¹
   distance one (an oriented nearest-neighbour bond `s → t`), and the single jump `J_x = b S_x`;
   in particular `H = 0`;
4. every site belongs to at most two bonds (constant incidence).

**Formalization Note** The generator is `gen I = Σ_x 𝒟_{J_x}`; the rate is `γ := b²`. The
instance's own `T` and `ϵ` fields are not used: Theorem 6.1 evolves for the real time
`T = θ/γ`. -/
structure IsTransportInstance {D : ℕ} {hD : 1 ≤ D} (L : ℕ) (b : ℚ)
    (I : Instance (transportParams D hD)) : Prop where
  sites_nodup : I.sites.Nodup
  sites_cube : ∀ x, x ∈ I.sites ↔ InCube D L x
  b_pos : 0 < b
  b_dyadic : ∃ m k : ℕ, b = (m : ℚ) / 2 ^ k
  bonds : ∀ t ∈ I.terms, ∃ s u : Fin D → ℤ, InCube D L s ∧ InCube D L u ∧ l1dist s u = 1 ∧
    t = (⟨[s, u], TermData.jump [transportJ b]⟩ : Term (transportParams D hD))
  incidence : ∀ x : Fin D → ℤ, ∀ s : Finset (Fin I.nT), (∀ e ∈ s, x ∈ (I.term e).supp) → s.card ≤ 2

/-- The depth radius `R₁(θ, E) := θ + E / log(e + E/θ)` (§6.1, p.51; natural logarithm). -/
noncomputable def radius1 (θ E : ℝ) : ℝ := θ + E / Real.log (Real.exp 1 + E / θ)

/-- The fixed-schedule radius `R_{D+1}(θ, E) := θ + (E / log(e + E/θ^{D+1}))^{1/(D+1)}` (§6.1,
p.51; natural logarithm). -/
noncomputable def radiusD1 (D : ℕ) (θ E : ℝ) : ℝ :=
  θ + (E / Real.log (Real.exp 1 + E / θ ^ (D + 1))) ^ ((1 : ℝ) / ((D : ℝ) + 1))

end Supplement

end LindbladShallow


