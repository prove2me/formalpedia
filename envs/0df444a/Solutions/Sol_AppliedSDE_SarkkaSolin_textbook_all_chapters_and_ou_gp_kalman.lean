-- Prove2me | solution 1 for AppliedSDE.SarkkaSolin.textbook_all_chapters_and_ou_gp_kalman
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T22:27:30.172741+00:00
-- url     : https://prove2.me/submissions/9e1b94cc-813e-45fc-8a30-7f93a61db0fa
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_AppliedSDE_SarkkaSolin_ChapterCertification02to05
import Definitions.Def_AppliedSDE_SarkkaSolin_ChapterCertification06to09
import Definitions.Def_AppliedSDE_SarkkaSolin_ChapterCertification10to12AndGP
import Theorems.Thm_AppliedSDE_SarkkaSolin_scalar_linear_ode_variation_constants
import Theorems.Thm_AppliedSDE_SarkkaSolin_ou_exact_stochastic_integral_transition_moments
import Theorems.Thm_AppliedSDE_SarkkaSolin_time_dependent_multivariate_ito_formula
import Theorems.Thm_AppliedSDE_SarkkaSolin_stationary_gradient_fpk_multivariate
import Theorems.Thm_AppliedSDE_SarkkaSolin_ou_exponential_kernel_psd
import Theorems.Thm_AppliedSDE_SarkkaSolin_girsanov_brownian_shift_terminal_density
import Theorems.Thm_AppliedSDE_SarkkaSolin_euler_maruyama_strong_half_order
import Theorems.Thm_AppliedSDE_SarkkaSolin_multivariate_stein_linear_gaussian
import Theorems.Thm_AppliedSDE_SarkkaSolin_scalar_kalman_bucy_riccati_nonnegative
import Theorems.Thm_AppliedSDE_SarkkaSolin_ou_gaussian_path_log_likelihood
import Theorems.Thm_AppliedSDE_SarkkaSolin_covariance_kernel_sum_and_product_psd
import Theorems.Thm_AppliedSDE_SarkkaSolin_stationary_ou_gp_batch_equals_kalman
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
universe u

theorem solution :
    private_sde_cert_ch02 ∧
    private_sde_cert_ch03.{u} ∧
    private_sde_cert_ch04.{u} ∧
    private_sde_cert_ch05 ∧
    private_sde_cert_ch06 ∧
    private_sde_cert_ch07.{u} ∧
    private_sde_cert_ch08.{u} ∧
    private_sde_cert_ch09 ∧
    private_sde_cert_ch10 ∧
    private_sde_cert_ch11 ∧
    private_sde_cert_ch12 ∧
    private_sde_cert_gp := by
  exact ⟨
    AppliedSDE.SarkkaSolin.scalar_linear_ode_variation_constants,
    AppliedSDE.SarkkaSolin.ou_exact_stochastic_integral_transition_moments,
    AppliedSDE.SarkkaSolin.time_dependent_multivariate_ito_formula,
    AppliedSDE.SarkkaSolin.stationary_gradient_fpk_multivariate,
    AppliedSDE.SarkkaSolin.ou_exponential_kernel_psd,
    AppliedSDE.SarkkaSolin.girsanov_brownian_shift_terminal_density,
    AppliedSDE.SarkkaSolin.euler_maruyama_strong_half_order,
    AppliedSDE.SarkkaSolin.multivariate_stein_linear_gaussian,
    AppliedSDE.SarkkaSolin.scalar_kalman_bucy_riccati_nonnegative,
    AppliedSDE.SarkkaSolin.ou_gaussian_path_log_likelihood,
    AppliedSDE.SarkkaSolin.covariance_kernel_sum_and_product_psd,
    AppliedSDE.SarkkaSolin.stationary_ou_gp_batch_equals_kalman
  ⟩
