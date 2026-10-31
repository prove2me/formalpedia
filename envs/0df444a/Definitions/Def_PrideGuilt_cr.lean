-- Prove2me | Definitions.Def_PrideGuilt_cr
-- name    : PrideGuilt_cr
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:54:47.142982+00:00
-- url     : https://prove2.me/theorems/2817fc7c-1fce-4cb9-96fd-61b03c2a6ee8
-- title:
--   Net personal cost of recycling $c_r=c_e-I_P-I_G$
-- statement:
--   The consumer's net personal cost of recycling is
--
--   $$
--   c_r \equiv c_e - I_P - I_G ,
--   $$
--
--   the recycling cost $c_e$ less the intrinsic pride $I_P$ of recycling and the intrinsic guilt $I_G$ avoided by recycling. Lemma 1 locates the equilibrium recycling rate by comparing the reward $f$ with $c_r-\gamma_P$ and $c_r-\gamma_G$, and $c_r-\Delta c$ is the paper's difficulty of remanufacturing.
-- source:
--   W. Huang, J. Nguyen, C.-L. Tseng, W. Chen, S. N. Kirshner, Pride or Guilt? Impacts of Consumers' Socially Influenced Recycling Behaviors on Closed-Loop Supply Chains, Manufacturing & Service Operations Management 26(6) (2024), doi:10.1287/msom.2023.0721 (accepted manuscript, printed page = PDF page - 1), Lemma 1, p.9

import Mathlib
import Definitions.Def_PrideGuilt_Params

namespace PrideGuilt

/-- **The consumer's net personal cost of recycling, `c_r ≡ c_e − I_P − I_G`.**
Huang–Nguyen–Tseng–Chen–Kirshner, *Pride or Guilt?*, M&SOM 26(6) (2024), doi:10.1287/msom.2023.0721, Lemma 1, p.9 (PDF 10). -/
def cr (P : Params) : ℝ := P.ce - P.IP - P.IG

end PrideGuilt


