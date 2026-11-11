-- Prove2me | Definitions.Def_LindbladShallow_localDecomp
-- name    : LindbladShallow_localDecomp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T04:21:26.124857+00:00
-- url     : https://prove2.me/theorems/4dafb1d3-2703-40cc-86f4-32d67f4b4a42
-- title:
--   Eq. (11) parameters, coarse cubes, colours, envelopes, hosts, local factors and window calls
-- statement:
--   With $\chi=8^D$, Eq. (11) sets $N_0=\max\{1,\lceil4096\kappa a\rceil\}$, $\tau=T/N_0$, $m_*=1+\lceil\log_8(4096\chi^2nN_0^2/\epsilon^2)\rceil$, $R=2r_*m_*$. A term is owned by the cube $C_R(e)=(\lfloor a(e)_1/R\rfloor,\dots,\lfloor a(e)_D/R\rfloor)$ of its anchor $a(e)$ (first support site); $C_\Lambda$ is the set of owner cubes of retained terms; cubes are coloured modulo $8$ in each coordinate. The **envelope** is $\Omega_C=B_C^{+(R+2r_*)}\cap\Lambda$ with $B_C=(RC+[0,R)^D)\cap\mathbb Z^D$, and the **complete host** is $RC+[-3R,4R)^D$.
--
--   $U_c$ activates the terms of colour at most $c$; the local factor of owner $C$ of colour $c$ is $W_C=U_{c,\Omega_C}U_{c-1,\Omega_C}^\dagger$; $W_{\mathrm{loc}}=D^{\mathrm{loc}}_\chi\cdots D^{\mathrm{loc}}_1$ with $D^{\mathrm{loc}}_c=\prod_{\mathrm{colour}(C)=c}W_C$. With $r$ windows of $M/r$ periods, $W_C=V^{(c)}_{C,r}\cdots V^{(c)}_{C,1}V^{(c-1)\dagger}_{C,1}\cdots V^{(c-1)\dagger}_{C,r}$ (Eq. (16)), executed as window calls; $Y_{\mathrm{in}}$ is the prefix isometry before a call, and $\mathcal B_{\mathrm{cat}}(C)$ is the set of bath labels of the owners within $\ell^\infty$ distance $3$ of $C$.
--
--   These are the objects of Corollary 3.5 and Theorem 3.7.
--
--   **Formalization Note** The colour of $C$ is $1+\sum_j(C_j\bmod 8)8^j$, one fixed enumeration of $(\mathbb Z/8)^D$. The owners of one colour are taken in the order of a given list.
-- source:
--   Shen, Wu, Yuan, Zhang, Shallow Quantum Circuits for Geometrically Local Lindblad Dynamics, arXiv:2610.05362 (held version, sha256 8f4637ef…), §3.2, pp.17–18, Eq. (11); §3.3, pp.19–20, Eqs. (15)–(16)

import Mathlib
import Definitions.Def_LindbladShallow_collision
import Definitions.Def_LindbladShallow_lam

open scoped Matrix ComplexOrder

namespace LindbladShallow

/-- The number of colour layers `χ = 8^D` (arXiv:2610.05362, held version sha256 8f4637ef…,
§3.2, p.17). -/
def chi (P : Params) : ℕ := 8 ^ P.D

/-- `N₀ = max{1, ⌈4096 κ a⌉}`, `a = λT`, the number of segments (Eq. (11), p.18). -/
noncomputable def N0 {P : Params} (I : Instance P) : ℕ :=
  max 1 ⌈4096 * (P.κ : ℝ) * (lam I * (I.T : ℝ))⌉₊

/-- The segment duration `τ = T/N₀` (Eq. (11)). -/
noncomputable def tau {P : Params} (I : Instance P) : ℝ := (I.T : ℝ) / (N0 I : ℝ)

/-- `m∗ = 1 + ⌈log₈(4096 χ² n N₀² / ϵ²)⌉` (Eq. (11), p.18).

**Formalization Note** The page computes it as `1 + k` with `k ≥ 0` the least integer with
`8^k ≥ A`, `A = 4096χ²nN₀²/ϵ² ≥ 4096`; this is `1 + ⌈log₈ A⌉₊`. -/
noncomputable def mstarE {P : Params} (I : Instance P) : ℕ :=
  1 + ⌈Real.logb 8 (4096 * (chi P : ℝ) ^ 2 * (I.n : ℝ) * (N0 I : ℝ) ^ 2 / (I.ε : ℝ) ^ 2)⌉₊

/-- The coarse-graining length `R = 2 r∗ m∗` (Eq. (11)). -/
noncomputable def Rlen {P : Params} (I : Instance P) : ℕ := 2 * P.rstar * mstarE I

/-- The anchor `a(e)` of a term, its first support site in input order (§2.1, p.9). -/
def anchor {P : Params} (t : Term P) : Site P := t.supp.headD 0

/-- The owner cube `C_R(e) = (⌊a(e)_1/R⌋, …, ⌊a(e)_D/R⌋)` of a term (p.9; Euclidean division). -/
def owner {P : Params} (R : ℕ) (t : Term P) : Fin P.D → ℤ :=
  fun j => anchor t j / (R : ℤ)

/-- `C_Λ := {C ∈ ℤ^D : B_C contains the anchor of a retained term}`, the assigned coarse cubes
(p.17). -/
noncomputable def CLam {P : Params} (I : Instance P) (R : ℕ) : Finset (Fin P.D → ℤ) :=
  open Classical in
  (Finset.univ.filter fun e : Fin I.nT => (I.term e).Retained).image fun e => owner R (I.term e)

/-- The colour of a coarse cube, modulo eight in each coordinate: `1 + Σ_j (C_j mod 8)·8^j ∈
{1, …, 8^D}` (p.17).

**Formalization Note** The page colours cubes "modulo eight, giving χ = 8^D" without fixing the
order of the colours; this is one fixed enumeration of `(ℤ/8)^D`. -/
def colour {P : Params} (C : Fin P.D → ℤ) : ℕ :=
  1 + ∑ j : Fin P.D, (C j % 8).toNat * 8 ^ (j : ℕ)

/-- `x ∈ B_C^{+s}`: `x` is within ℓ∞ distance `s` of the cube `B_C = (RC + [0, R)^D) ∩ ℤ^D` (p.17). -/
def InEnv {P : Params} (R : ℕ) (C : Fin P.D → ℤ) (s : ℤ) (x : Site P) : Prop :=
  ∀ j, (R : ℤ) * C j - s ≤ x j ∧ x j ≤ (R : ℤ) * C j + (R : ℤ) - 1 + s

/-- The envelope `Ω_C := B_C^{+(R + 2r∗)} ∩ Λ` of owner `C` (p.17). -/
def OmegaC {P : Params} (I : Instance P) (R : ℕ) (C : Fin P.D → ℤ) : Set (Site P) :=
  {x | x ∈ I.sites ∧ InEnv R C ((R : ℤ) + 2 * (P.rstar : ℤ)) x}

/-- The complete host of owner `C` at coarse level: the cubes `C'` with `‖C' − C‖_∞ ≤ 3`, i.e. the box
`RC + [−3R, 4R)^D` (p.17, p.19 and Figure 2). -/
def hostC {P : Params} (R : ℕ) (C : Fin P.D → ℤ) : Set (Site P) :=
  {x | ∀ j, (R : ℤ) * C j - 3 * (R : ℤ) ≤ x j ∧ x j < (R : ℤ) * C j + 4 * (R : ℤ)}

/-- Activation mask of `U_c`: the terms whose owner has colour at most `c` (p.17; `U_0 = I`). -/
def actUpTo {P : Params} (I : Instance P) (R c : ℕ) : Fin I.nT → Prop :=
  fun e => colour (owner R (I.term e)) ≤ c

/-- The word of the local factor `W_C := U_{c,Ω_C} U_{c−1,Ω_C}†` of owner `C` of colour `c`: the
inverse old pass, then the new forward pass, on the permanent baths (p.17). -/
noncomputable def factorWord {P : Params} (I : Instance P) (M R : ℕ) (C : Fin P.D → ℤ) :
    Word I M :=
  adjWord (fwdWord I M (actUpTo I R (colour C - 1)) (OmegaC I R C) (List.finRange M)) ++
    fwdWord I M (actUpTo I R (colour C)) (OmegaC I R C) (List.finRange M)

/-- The word of the localized segment circuit `W_loc := D_χ^loc ⋯ D_1^loc`,
`D_c^loc := ∏_{C ∈ C_Λ : colour(C) = c} W_C` (p.18), with the owners of each colour taken in the
order of the list `ord` (`D_1` acts first). -/
noncomputable def locWord {P : Params} (I : Instance P) (M R : ℕ) (ord : List (Fin P.D → ℤ)) :
    Word I M :=
  (List.range' 1 (chi P)).flatMap fun c =>
    (ord.filter fun C => colour C = c).flatMap fun C => factorWord I M R C

/-- The periods of window `j` (`0 ≤ j < r`), the `j`-th group of `M/r` consecutive periods
(p.11 and Eq. (16), p.20). -/
def windowPeriods (M r j : ℕ) : List (Fin M) :=
  (List.finRange M).filter fun m => j * (M / r) ≤ m.val ∧ m.val < (j + 1) * (M / r)

/-- The forward window `V^{(c)}_{C,j+1}`: the forward circuit on window `j` with colour mask `c`,
restricted to `Ω_C` (Eq. (16), p.20). -/
noncomputable def winWord {P : Params} (I : Instance P) (M R r c : ℕ) (C : Fin P.D → ℤ)
    (j : ℕ) : Word I M :=
  fwdWord I M (actUpTo I R c) (OmegaC I R C) (windowPeriods M r j)

/-- The window calls of the factor `W_C = V^{(c)}_{C,r} ⋯ V^{(c)}_{C,1} V^{(c−1)†}_{C,1} ⋯
V^{(c−1)†}_{C,r}` (Eq. (16), p.20): old inverse windows `r` to `1`, then new forward windows `1` to
`r`. Each call is (owner, forward window word `V`, inverse flag); an inverse call applies `V†`. -/
noncomputable def factorCalls {P : Params} (I : Instance P) (M R r : ℕ) (C : Fin P.D → ℤ) :
    List ((Fin P.D → ℤ) × Word I M × Bool) :=
  ((List.range r).reverse.map fun j => (C, winWord I M R r (colour C - 1) C j, true)) ++
    ((List.range r).map fun j => (C, winWord I M R r (colour C) C j, false))

/-- All window calls of the localized segment circuit, in colour order and, within a colour, in the
owner order `ord` (p.20). -/
noncomputable def callList {P : Params} (I : Instance P) (M R r : ℕ) (ord : List (Fin P.D → ℤ)) :
    List ((Fin P.D → ℤ) × Word I M × Bool) :=
  (List.range' 1 (chi P)).flatMap fun c =>
    (ord.filter fun C => colour C = c).flatMap fun C => factorCalls I M R r C

/-- The word actually applied by a call: `V`, or `V†` for an inverse call. -/
def callImpl {P : Params} {I : Instance P} {M : ℕ} (x : (Fin P.D → ℤ) × Word I M × Bool) :
    Word I M :=
  if x.2.2 then adjWord x.2.1 else x.2.1

/-- The ideal global prefix isometry `Y_in` immediately before call `k`: all preceding localized
windows applied to the shared vacuum, `Y_in = (preceding calls) E₀` (p.20). -/
noncomputable def prefixY {P : Params} (I : Instance P) (M R r : ℕ) (h : ℝ)
    (ord : List (Fin P.D → ℤ)) (k : ℕ) : Matrix (Tot I M) (Sys I) ℂ :=
  wordU I M h (((callList I M R r ord).take k).flatMap callImpl) * E0 I M

/-- The complete local bath set `B_cat` of factor `C`: all bath labels, over all periods, of the
terms whose owner cube `C'` has `‖C' − C‖_∞ ≤ 3` (p.19). -/
noncomputable def Bcat {P : Params} (I : Instance P) (M R : ℕ) (C : Fin P.D → ℤ) :
    Finset (BJ I M) :=
  open Classical in
  Finset.univ.filter fun b => ∀ j, |owner R (I.term b.1.1) j - C j| ≤ 3

end LindbladShallow


