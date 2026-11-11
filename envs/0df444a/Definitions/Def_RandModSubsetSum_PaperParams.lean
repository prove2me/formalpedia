-- Prove2me | Definitions.Def_RandModSubsetSum_PaperParams
-- name    : RandModSubsetSum_PaperParams
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T22:02:39.497192+00:00
-- url     : https://prove2.me/theorems/7d777cd5-1ff3-4e7e-b6bd-d26237dbab62
-- title:
--   The paper's parameters: Gaussian numerators (Tables 2–4), the kernels (37)–(38), rates $K_i$ (Table 5) and $\gamma$
-- statement:
--   The explicit nominal kernels of §6. For a nonnegative parent symbol $c$ at depth $j$, $C_{j,c}=\{(a,b)\in A_{j+1}^2:a+b=c\}$ and $e_c(a,b)=((a-b)^2-(c\bmod 2))/4$. For a listed numerator $N=N^{(r)}_{j,c}$ (Tables 2–4: $j=0$: $c\le1$; $j=1$: $c\le 3$; $j=2,3$: $c\le2$; $j=4,5,6$: $c=0$) and $\zeta=N/10^{10}$:
--
--   1. the rational Gaussian (37) $G(a,b)=\zeta^{e_c(a,b)}/\sum_{(u,v)\in C_{j,c}}\zeta^{e_c(u,v)}$ with $0^0=1$;
--   2. the smoothing $R^*=(1-\epsilon_{\rm ker})G+\epsilon_{\rm ker}/|C_{j,c}|$, $\epsilon_{\rm ker}=10^{-12}$;
--   3. the $10^{20}$-type approximation (38) over the reversal orbits $O=\{(a,b),(b,a)\}$, ordered by $(|a-b|,a,b)$ of the representative $a\le b$, split equally inside an orbit: $R((a,b)\mid c)=\lfloor\Pi\rceil_{10^{20}}(O)/|O|$.
--
--   An unlisted nonnegative parent symbol gets the uniform distribution on $C_{j,c}$; for $j\ge1$ and $c>0$, $R((-a,-b)\mid -c)=R((a,b)\mid c)$; all other cells are $0$.
--
--   The rates $K_1,\dots,K_7$ are the exact decimals of Table 5 ($K_8=0$), and $\gamma=0.000001000026$ is the certified gap of (41). Together with the weights $W_r/10^{20}$ these are the parameters for which (41) asserts the hypotheses of Lemma 4.3.
--
--   **Formalization Note** Table entries are transcribed as integers; the decimals of Table 5 are exact rationals. Recomputing the nominal $H_i$ and $D_j$ at $\rho_r=1/2$ from these definitions reproduces Table 6 to all nine printed decimals.
-- source:
--   Kim, Kim, Lee, Faster Provable Algorithm For Random Modular Subset Sum, STOC 2027 submission manuscript (sha256 c37a38c7…f89), §6.1–6.2, Tables 2–5, (37)–(38), pp. 41–44; (41), p. 49

import Mathlib
import Definitions.Def_RandModSubsetSum_Types
import Definitions.Def_RandModSubsetSum_Strata
import Definitions.Def_RandModSubsetSum_Template
import Definitions.Def_RandModSubsetSum_Kernels

open scoped BigOperators

namespace RandModSubsetSum

/-! The explicit parameters of §6 (Kim, Kim, Lee, *Faster Provable Algorithm For Random Modular
Subset Sum*, STOC 2027 submission manuscript (sha256 c37a38c7…f89), §6.1–6.2, pp. 41–44): the 195
Gaussian numerators of Tables 2–4, the rates of Table 5, and the construction rules (37)–(38). -/

/-- Gaussian numerators `N^{(r)}_{j,c}`: Table 2, columns `j = 0`, `c = 0, 1` (pp. 41–42). Row `r − 1` is stratum `r`. -/
def paperN0 : Fin 13 → Fin 2 → ℕ :=
  ![![3218996852, 3333858578],
    ![2979264813, 3121972775],
    ![726676153, 1302484035],
    ![941589060, 1514713006],
    ![2776830974, 2953757303],
    ![2772284045, 2951377082],
    ![703907864, 1275189842],
    ![2884304088, 3049495778],
    ![2950769217, 3098168118],
    ![712205135, 1286561599],
    ![733228049, 1313361943],
    ![712286520, 1291762292],
    ![722723757, 1300678863]]

/-- Gaussian numerators `N^{(r)}_{j,c}`: Table 2, columns `j = 1`, `c = 0, 1, 2, 3` (pp. 41–42). Row `r − 1` is stratum `r`. -/
def paperN1 : Fin 13 → Fin 4 → ℕ :=
  ![![3619527636, 3892148563, 3959024029, 4344534110],
    ![3564795730, 3900083591, 3955581168, 2241289311],
    ![220606869, 182410979, 109868368, 181862451],
    ![289719049, 249714528, 145870691, 181862538],
    ![3247932700, 3600590787, 3476440105, 24758847],
    ![3241964451, 3593326595, 3473065179, 24718373],
    ![213694216, 139013845, 87578028, 181862500],
    ![3540809549, 3909681573, 3968432459, 4248897718],
    ![3568600093, 3909677554, 3977535148, 2127761488],
    ![216198484, 169157365, 102754350, 181855467],
    ![222437530, 173459366, 140051229, 163494437],
    ![216116997, 199124395, 152838126, 181927909],
    ![219263617, 167001771, 137858599, 163485577]]

/-- Gaussian numerators `N^{(r)}_{j,c}`: Table 3, columns `j = 2`, `c = 0, 1, 2` (pp. 41–42). Row `r − 1` is stratum `r`. -/
def paperN2 : Fin 13 → Fin 3 → ℕ :=
  ![![4494536862, 4586245163, 4773032640],
    ![4463751370, 4561206297, 4668986720],
    ![146451802, 3373110, 2044494],
    ![224512187, 3382994, 2056709],
    ![3097983034, 3085470918, 3247356359],
    ![3027843483, 3008959788, 3076040780],
    ![130473310, 3386046, 2051316],
    ![4500694635, 4602380934, 4658920111],
    ![4527469305, 4629764681, 4786367328],
    ![135093086, 3383894, 2051231],
    ![136896039, 3524767, 1789348],
    ![129517842, 3430881, 2060972],
    ![134219999, 3591990, 1785073]]

/-- Gaussian numerators `N^{(r)}_{j,c}`: Table 3, columns `j = 3`, `c = 0, 1, 2` (pp. 41–42). Row `r − 1` is stratum `r`. -/
def paperN3 : Fin 13 → Fin 3 → ℕ :=
  ![![4462422051, 4522931850, 4438177799],
    ![4576939997, 4680734163, 4902647855],
    ![71022552, 28149287, 141],
    ![145909683, 28173629, 141],
    ![1508639021, 2934484, 671],
    ![1462694826, 2928664, 670],
    ![50942728, 28565158, 141],
    ![4668457010, 4796748097, 5220077131],
    ![4272858419, 4316676779, 4285882059],
    ![60680778, 28668554, 141],
    ![54594750, 27204630, 171],
    ![52138926, 27749492, 141],
    ![52717017, 25359703, 171]]

/-- Gaussian numerators `N^{(r)}_{j,c}`: Table 4, column `N^{(r)}_{4,0}` (pp. 41–42). Row `r − 1` is stratum `r`. -/
def paperN4 : Fin 13 → ℕ :=
  ![3198800564, 4665539937, 9656248, 4907370057, 3197717301, 3624155000, 25838511, 4238240231, 3216764230, 15251917, 152665, 225682, 157847]

/-- Gaussian numerators `N^{(r)}_{j,c}`: Table 4, column `N^{(r)}_{5,0}` (pp. 41–42). Row `r − 1` is stratum `r`. -/
def paperN5 : Fin 13 → ℕ :=
  ![586268, 2824739395, 199, 199, 683136330, 774947443, 199, 2967481167, 2708401259, 199, 230, 199, 231]

/-- Gaussian numerators `N^{(r)}_{j,c}`: Table 4, column `N^{(r)}_{6,0}` (pp. 41–42). Row `r − 1` is stratum `r`. -/
def paperN6 : Fin 13 → ℕ :=
  ![0, 0, 0, 0, 29857372, 29568976, 0, 4408350480, 4481909195, 0, 0, 0, 28792]

/-- The listed numerator `N^{(r)}_{j,c}` for a nonnegative parent symbol `c` at depth `j`, if `c` is
listed in Tables 2–4 (`j = 0`: `c ≤ 1`; `j = 1`: `c ≤ 3`; `j = 2, 3`: `c ≤ 2`; `j = 4, 5, 6`: `c = 0`),
and `none` for an unlisted symbol. -/
def paperNum (j : ℕ) (r : Fin 13) (c : ℕ) : Option ℕ :=
  match j with
  | 0 => if h : c < 2 then some (paperN0 r ⟨c, h⟩) else none
  | 1 => if h : c < 4 then some (paperN1 r ⟨c, h⟩) else none
  | 2 => if h : c < 3 then some (paperN2 r ⟨c, h⟩) else none
  | 3 => if h : c < 3 then some (paperN3 r ⟨c, h⟩) else none
  | 4 => if c = 0 then some (paperN4 r) else none
  | 5 => if c = 0 then some (paperN5 r) else none
  | 6 => if c = 0 then some (paperN6 r) else none
  | _ => none

open Classical in
/-- `C_{j,c} = {(a, b) ∈ A_{j+1}² : a + b = c}` (§6.2, p. 43). -/
noncomputable def supportPairs (j : ℕ) (c : ℤ) : Finset (ℤ × ℤ) :=
  (childPairs j).filter (fun ab => ab.1 + ab.2 = c)

/-- The exponent `e_c(a, b) = ((a − b)² − (c mod 2)) / 4` (§6.2, p. 43), a nonnegative integer on
`C_{j,c}` for `c ≥ 0`. -/
def gaussExp (c : ℤ) (ab : ℤ × ℤ) : ℕ := (((ab.1 - ab.2) ^ 2 - c % 2) / 4).toNat

/-- The rational Gaussian distribution (37), p. 43:
`G^{(r)}_{j,c}(a, b) = ζ^{e_c(a,b)} / Σ_{(u,v) ∈ C_{j,c}} ζ^{e_c(u,v)}` with `ζ = N / 10¹⁰` and the
convention `0⁰ = 1` (natural-number powers). -/
noncomputable def gaussKernel (N : ℕ) (j : ℕ) (c : ℤ) (ab : ℤ × ℤ) : ℝ :=
  ((N : ℝ) / 10 ^ 10) ^ gaussExp c ab /
    ∑ uv ∈ supportPairs j c, ((N : ℝ) / 10 ^ 10) ^ gaussExp c uv

/-- The smoothed kernel `R* = (1 − ε_ker) G + ε_ker / |C_{j,c}|` with `ε_ker = 10⁻¹²` (§6.2, p. 44). -/
noncomputable def smoothKernel (N : ℕ) (j : ℕ) (c : ℤ) (ab : ℤ × ℤ) : ℝ :=
  (1 - 1 / 10 ^ 12) * gaussKernel N j c ab + (1 / 10 ^ 12) / ((supportPairs j c).card : ℝ)

/-- The mass `Π(O) = Σ_{(a,b) ∈ O} R*(a, b)` of the reversal orbit `O = {(a, b), (b, a)}`, given by
its representative `(a, b)` with `a ≤ b` (§6.2, p. 44). -/
noncomputable def orbitMass (N : ℕ) (j : ℕ) (c : ℤ) (ab : ℤ × ℤ) : ℝ :=
  smoothKernel N j c ab + (if ab.1 = ab.2 then 0 else smoothKernel N j c (ab.2, ab.1))

open Classical in
/-- The orbit representatives `(a, b) ∈ C_{j,c}` with `a ≤ b`. -/
noncomputable def orbitReps (j : ℕ) (c : ℤ) : Finset (ℤ × ℤ) :=
  (supportPairs j c).filter (fun ab => ab.1 ≤ ab.2)

/-- The tie-breaking order of (38), p. 44: orbits ordered by `(|a − b|, a, b)` of their
representative `a ≤ b`. -/
def orbitKey (ab : ℤ × ℤ) : Lex (ℤ × Lex (ℤ × ℤ)) := toLex (|ab.1 - ab.2|, toLex (ab.1, ab.2))

/-- The listed kernel (38), p. 44, for a nonnegative listed parent symbol `c`:
`R((a, b) | c) = ⌊Π⌉_{10²⁰}(O) / |O|` for `(a, b) ∈ O`, the `10²⁰`-type approximation of the orbit
masses with the order `(|a − b|, a, b)`, split equally inside an orbit. -/
noncomputable def listedKernel (N : ℕ) (j : ℕ) (c : ℤ) (ab : ℤ × ℤ) : ℝ :=
  typeRound (orbitReps j c) orbitKey (orbitMass N j c) (10 ^ 20) (min ab.1 ab.2, max ab.1 ab.2) /
    (if ab.1 = ab.2 then 1 else 2)

/-- The kernel for a nonnegative parent symbol `c ∈ A_j` and an allowed pair `(a, b) ∈ C_{j,c}`:
the listed kernel (38) if `N^{(r)}_{j,c}` is listed, else the uniform distribution
`1 / |C_{j,c}|` (§6.2, p. 44). -/
noncomputable def nonnegKernel (j : ℕ) (r : Fin 13) (c : ℤ) (ab : ℤ × ℤ) : ℝ :=
  match paperNum j r c.toNat with
  | some N => listedKernel N j c ab
  | none => 1 / ((supportPairs j c).card : ℝ)

open Classical in
/-- **The paper's nominal kernels** `R^{(r)}_j((a, b) | c)` (§6.2, pp. 43–44): for `0 ≤ j ≤ 6`,
`c ∈ A_j`, `(a, b) ∈ A_{j+1}²` with `a + b = c`, the nonnegative-symbol rule for `c ≥ 0` and the
sign reflection `R((−a, −b) | −c) = R((a, b) | c)` for `c < 0` (only `j ≥ 1` has negative parent
symbols); "All other cells have probability zero." -/
noncomputable def paperKernel : Kernel := fun j r c ab =>
  if j < 7 ∧ c ∈ alph j ∧ ab.1 ∈ alph (j + 1) ∧ ab.2 ∈ alph (j + 1) ∧ ab.1 + ab.2 = c then
    (if 0 ≤ c then nonnegKernel j r c ab else nonnegKernel j r (-c) (-ab.1, -ab.2))
  else 0

/-- The cumulative residue rates `K_1, …, K_7` of Table 5 (p. 42; the row `j` lists `K_{j+1}`), as
exact decimals; index `i` holds `K_{i+1}`. `K_8 = 0`. -/
noncomputable def paperK : Fin 7 → ℝ :=
  ![999989594580 / 10 ^ 12, 994490012926 / 10 ^ 12, 868832396690 / 10 ^ 12,
    723896625384 / 10 ^ 12, 534799548745 / 10 ^ 12, 443720708787 / 10 ^ 12,
    253400372539 / 10 ^ 12]

/-- The certified gap `γ := 0.000001000026` of (41), p. 49. -/
noncomputable def paperGamma : ℝ := 1000026 / 10 ^ 12

end RandModSubsetSum


