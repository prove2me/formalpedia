-- Prove2me | Definitions.Def_DNFSatMQ_Main_Scan
-- name    : DNFSatMQ_Main_Scan
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T23:32:29.257447+00:00
-- url     : https://prove2.me/theorems/21c8fb8e-7edd-4400-8d1f-0bae2ceae8d5
-- title:
--   The scan (Algorithm 3), its update maps g_i and Φ_{π,r}, the events H_k and counts E, L of §5, and Algorithm 4 with parameters (10)
-- statement:
--   The objects of §5 (pp. 14–21) and §7 (pp. 26–27). Throughout, $F \subseteq \{0,1\}^n$ is the satisfying set of the target and membership queries are membership tests in $F$.
--
--   **Scan** (Algorithm 3). From $x \in F$ and a permutation $\pi$ of the coordinates, the scan examines the coordinates in the order $\pi(1), \dots, \pi(n)$ (here $\pi\,0, \dots, \pi\,(n-1)$): at step $t$ with $i = \pi(t)$ and current point $z$, if $z^{\oplus i} \notin F$ then $i$ is **rejected**, otherwise $z \leftarrow z^{\oplus i}$. It returns $c_I$, fixing the rejected coordinates $I$ to their values in $x$ (`scanConj`).
--
--   **Update maps** (§5.1). $g_i(z) = z^{\oplus i}$ if $z^{\oplus i}\in F$ and $z$ otherwise; $\Phi_{\pi,0} = \mathrm{id}$ and $\Phi_{\pi,r} = g_{\pi(r)}\circ\cdots\circ g_{\pi(1)}$ (`scanPrefix`), so the scan visits $z_r = \Phi_{\pi,r}(x)$. $\pi_{rev}(t) = \pi(n-t+1)$ (`permRev`). `withPerm p` is the law of $(x,\pi)$ with $x \sim p$ and an independent uniform $\pi \sim U_{S_n}$.
--
--   **Events and counts** (§5.2–5.3), for $f = \bigvee_{c'\in T} c'$ and a fixed $c_\star \in T$: $K_{c'} = \mathrm{Fix}(c') \cap \mathrm{Free}(c_\star)$; $H_k$ is the event that every visited point $z_0,\dots,z_n$ satisfies some $c' \in T$ with $|K_{c'}| \le k$; $E_{c_\star} = |\mathrm{Fix}(c_\star)\setminus I|$ and $L_{c_\star} = |I \cap \mathrm{Free}(c_\star)|$.
--
--   **Algorithm 4** and the parameters (10), for a constant $a_0$, $s \ge 1$ and $\varepsilon,\delta\in(0,1)$:
--   $$\theta = \frac{\varepsilon}{2s},\quad w = \Big\lceil a_0 \log_2 \frac{16 s}{\theta^2}\Big\rceil,\quad \tau = 2^{-w},\quad N_0 = \lceil 64\cdot 8^w\theta^{-3}\rceil,\quad N = N_0\Big\lceil \log_2\frac{2s}{\delta}\Big\rceil,\quad M = \Big\lceil 8\tau^{-2}\ln\frac{4N}{\delta}\Big\rceil,$$
--   and $\gamma(s,1/\varepsilon,1/\delta) = \tau/(4N)$. For $j = 1,\dots,N$: draw $x_j \sim U_F$, compute $c \leftarrow \mathrm{Scan}(x_j)$ with a uniform $\pi$, draw $y_1,\dots,y_M \sim U_C$ by giving the free coordinates of $c$ independent uniform bits, and append $c$ if $\hat p_c = M^{-1}\sum_t \mathrm{MQ}_f(y_t) \ge \tau/2$. `algorithm4` is the law of the output list.
--
--   **Formalization Note.** Coordinates and scan steps are $0$-based. Algorithm 4 is a probability law with exact uniform choices (finding I1 of the mission explains why it is not a machine run).
-- source:
--   Zelin Li, Learning DNF from Satisfying Assignments with Membership Queries, STOC 2027 submission (manuscript sha256 2e246dc4…2670), Algorithm 3, §5.1–5.3 and Algorithm 4 with (10), p. 14 (PDF 15); pp. 15–21 and 26–27 (PDF 16–22, 27–28)

import Mathlib
import Definitions.Def_DNFSatMQ_Main_Basic

namespace DNFSatMQ.Main

/-! The scan (Algorithm 3, p. 14), its update maps (§5.1, p. 15), the events and counts of §5
(pp. 15–21), and the densifier Algorithm 4 with its parameters (10) (pp. 26–27). Coordinates and
scan steps are `0`-based: the paper's step `t ∈ {1, …, n}` examines `π(t)`, here step `t ∈ {0, …,
n-1}` examines `π t`. Membership queries `MQ_f` are membership tests in `F = f⁻¹(1)`. -/

/-- `g_i(z) = z^{⊕i}` if `z^{⊕i} ∈ F`, and `z` otherwise (§5.1, p. 15). -/
def gUpdate {n : ℕ} (F : Finset (Pt n)) (i : Fin n) (z : Pt n) : Pt n :=
  if flipAt z i ∈ F then flipAt z i else z

/-- `Φ_{π,r} = g_{π(r)} ∘ ⋯ ∘ g_{π(1)}`, `Φ_{π,0} = id` (p. 15): the state `z_r` of the scan after
its first `r` steps (steps beyond `n` do nothing). -/
def scanPrefix {n : ℕ} (F : Finset (Pt n)) (π : Equiv.Perm (Fin n)) : ℕ → Pt n → Pt n
  | 0, z => z
  | r + 1, z => if h : r < n then gUpdate F (π ⟨r, h⟩) (scanPrefix F π r z) else scanPrefix F π r z

/-- The rejected coordinates `I` of `Scan(x)` with permutation `π` (Algorithm 3, p. 14): the
coordinate `i = π(t)` is rejected when `MQ_f(z_t^{⊕i}) = 0`, `z_t` being the state before step
`t`. -/
def rejected {n : ℕ} (F : Finset (Pt n)) (x : Pt n) (π : Equiv.Perm (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter fun i => flipAt (scanPrefix F π (π.symm i) x) i ∉ F

/-- The conjunction `c_I` returned by `Scan(x)`: it fixes each rejected coordinate to its value in
`x`. -/
def scanConj {n : ℕ} (F : Finset (Pt n)) (x : Pt n) (π : Equiv.Perm (Fin n)) : Conj n :=
  conjOfFix x (rejected F x π)

/-- `π_rev(t) = π(n − t + 1)` (Lemma 5.3), i.e. `π_rev t = π (n − 1 − t)` with `0`-based steps. -/
def permRev {n : ℕ} (π : Equiv.Perm (Fin n)) : Equiv.Perm (Fin n) := Fin.revPerm.trans π

/-- The law of `(x, π)` with `x ∼ p` and an independent uniform permutation `π ∼ U_{S_n}`. -/
noncomputable def withPerm {n : ℕ} (p : PMF (Pt n)) : PMF (Pt n × Equiv.Perm (Fin n)) :=
  p.bind fun x => (PMF.uniformOfFintype (Equiv.Perm (Fin n))).map fun π => (x, π)

/-- `K_{c'} = Fix(c') ∩ Free(c⋆)` (§5.2, p. 16). -/
def kSet {n : ℕ} (c' cstar : Conj n) : Finset (Fin n) := c'.fix ∩ cstar.free

/-- The event `H_k` (§5.2, p. 16) for the scan from `x` with permutation `π`, where
`f = ⋁_{c' ∈ T} c'`: each visited point `z_0, …, z_n` satisfies some `c' ∈ T` with
`|K_{c'}| ≤ k`. -/
def eventH {n : ℕ} (T : Finset (Conj n)) (cstar : Conj n) (k : ℕ) (x : Pt n)
    (π : Equiv.Perm (Fin n)) : Prop :=
  ∀ t : ℕ, t ≤ n → ∃ c' ∈ T, c'.Sat (scanPrefix (unionSet T) π t x) ∧ (kSet c' cstar).card ≤ k

/-- `E_{c⋆} = |Fix(c⋆) ∩ Free(c)| = |Fix(c⋆) \ I|` (p. 15). -/
def countE {n : ℕ} (T : Finset (Conj n)) (cstar : Conj n) (x : Pt n) (π : Equiv.Perm (Fin n)) :
    ℕ :=
  (cstar.fix \ rejected (unionSet T) x π).card

/-- `L_{c⋆} = |Fix(c) ∩ Free(c⋆)| = |I ∩ Free(c⋆)|` (p. 15). -/
def countL {n : ℕ} (T : Finset (Conj n)) (cstar : Conj n) (x : Pt n) (π : Equiv.Perm (Fin n)) :
    ℕ :=
  (rejected (unionSet T) x π ∩ cstar.free).card

/-! ## Algorithm 4 and the parameters (10) -/

/-- `θ = ε / (2s)`. -/
noncomputable def par_θ (s : ℕ) (ε : ℝ) : ℝ := ε / (2 * s)

/-- `w = ⌈a₀ log₂(16 s / θ²)⌉`. -/
noncomputable def par_w (a0 : ℝ) (s : ℕ) (ε : ℝ) : ℕ :=
  ⌈a0 * Real.logb 2 (16 * s / par_θ s ε ^ 2)⌉₊

/-- `τ = 2^{−w}`. -/
noncomputable def par_τ (a0 : ℝ) (s : ℕ) (ε : ℝ) : ℝ := (2 : ℝ)⁻¹ ^ par_w a0 s ε

/-- `N₀ = ⌈64 · 8^w θ^{−3}⌉`. -/
noncomputable def par_N0 (a0 : ℝ) (s : ℕ) (ε : ℝ) : ℕ :=
  ⌈64 * (8 : ℝ) ^ par_w a0 s ε * (par_θ s ε)⁻¹ ^ 3⌉₊

/-- `N = N₀ ⌈log₂(2s/δ)⌉`. -/
noncomputable def par_N (a0 : ℝ) (s : ℕ) (ε δ : ℝ) : ℕ :=
  par_N0 a0 s ε * ⌈Real.logb 2 (2 * s / δ)⌉₊

/-- `M = ⌈8 τ^{−2} ln(4N/δ)⌉`. -/
noncomputable def par_M (a0 : ℝ) (s : ℕ) (ε δ : ℝ) : ℕ :=
  ⌈8 * (par_τ a0 s ε)⁻¹ ^ 2 * Real.log (4 * par_N a0 s ε δ / δ)⌉₊

/-- `γ(s, 1/ε, 1/δ) = τ / (4N)` (p. 26). -/
noncomputable def par_γ (a0 : ℝ) (s : ℕ) (ε δ : ℝ) : ℝ :=
  par_τ a0 s ε / (4 * par_N a0 s ε δ)

/-- One iteration of the loop of Algorithm 4: draw `x ∼ U_F` (one call to `EX⁺_f`), draw `π ∼ U_{S_n}`
and compute `c ← Scan(x)`, draw `y₁, …, y_M ∼ U_C` by assigning independent uniform bits to the
free coordinates of `c`, set `p̂_c = M^{−1} Σ_t MQ_f(y_t)`, and keep `c` iff `p̂_c ≥ τ/2`. -/
noncomputable def densIter {n : ℕ} (F : Finset (Pt n)) (hF : F.Nonempty) (M : ℕ) (τ : ℝ) :
    PMF (Option (Conj n)) :=
  (PMF.uniformOfFinset F hF).bind fun x =>
    (PMF.uniformOfFintype (Equiv.Perm (Fin n))).bind fun π =>
      (PMF.uniformOfFintype (Fin M → Pt n)).map fun ys =>
        if τ / 2 ≤ ((Finset.univ.filter fun t : Fin M =>
              (scanConj F x π).fill (ys t) ∈ F).card : ℝ) / M
        then some (scanConj F x π) else none

/-- `j` independent iterations of the loop, appending the retained candidates in order. -/
noncomputable def densLoop {n : ℕ} (F : Finset (Pt n)) (hF : F.Nonempty) (M : ℕ) (τ : ℝ) :
    ℕ → PMF (List (Conj n))
  | 0 => PMF.pure []
  | j + 1 => (densLoop F hF M τ j).bind fun cs =>
      (densIter F hF M τ).map fun o => cs ++ o.toList

/-- **Algorithm 4** `A_den(n, s, ε, δ)` (p. 27) as the law of its output list, with exact uniform
choices, for the target with satisfying set `F ≠ ∅` and the constant `a₀`. -/
noncomputable def algorithm4 {n : ℕ} (a0 : ℝ) (s : ℕ) (ε δ : ℝ) (F : Finset (Pt n))
    (hF : F.Nonempty) : PMF (List (Conj n)) :=
  densLoop F hF (par_M a0 s ε δ) (par_τ a0 s ε) (par_N a0 s ε δ)

end DNFSatMQ.Main


